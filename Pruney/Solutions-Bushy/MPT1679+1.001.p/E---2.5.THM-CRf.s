%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1679+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:35 EST 2020

% Result     : Theorem 0.42s
% Output     : CNFRefutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  515 (16303633148201 expanded)
%              Number of clauses        :  503 (4652519435799 expanded)
%              Number of leaves         :    5 (5656037147413 expanded)
%              Depth                    :  147
%              Number of atoms          : 4799 (401656999757327 expanded)
%              Number of equality atoms :  460 (42085081952452 expanded)
%              Maximal formula depth    :  116 (   8 average)
%              Maximal clause size      : 1248 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( ! [X4] :
                      ( ( v1_finset_1(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(X2)) )
                     => ( X4 != k1_xboole_0
                       => r2_yellow_0(X1,X4) ) )
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ~ ( r2_hidden(X4,X3)
                          & ! [X5] :
                              ( ( v1_finset_1(X5)
                                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                             => ~ ( r2_yellow_0(X1,X5)
                                  & X4 = k2_yellow_0(X1,X5) ) ) ) )
                  & ! [X4] :
                      ( ( v1_finset_1(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(X2)) )
                     => ( X4 != k1_xboole_0
                       => r2_hidden(k2_yellow_0(X1,X4),X3) ) )
                  & r2_yellow_0(X1,X2) )
               => k2_yellow_0(X1,X3) = k2_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_waybel_0)).

fof(t57_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( ! [X4] :
                      ( ( v1_finset_1(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(X2)) )
                     => ( X4 != k1_xboole_0
                       => r2_yellow_0(X1,X4) ) )
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ~ ( r2_hidden(X4,X3)
                          & ! [X5] :
                              ( ( v1_finset_1(X5)
                                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                             => ~ ( r2_yellow_0(X1,X5)
                                  & X4 = k2_yellow_0(X1,X5) ) ) ) )
                  & ! [X4] :
                      ( ( v1_finset_1(X4)
                        & m1_subset_1(X4,k1_zfmisc_1(X2)) )
                     => ( X4 != k1_xboole_0
                       => r2_hidden(k2_yellow_0(X1,X4),X3) ) ) )
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r1_lattice3(X1,X2,X4)
                    <=> r1_lattice3(X1,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_waybel_0)).

fof(t49_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2,X3] :
          ( ( r2_yellow_0(X1,X2)
            & ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r1_lattice3(X1,X2,X4)
                <=> r1_lattice3(X1,X3,X4) ) ) )
         => k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_yellow_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(c_0_4,plain,(
    ! [X1,X3,X2] :
      ( epred1_3(X2,X3,X1)
    <=> ( ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_yellow_0(X1,X4) ) )
        & ! [X4] :
            ( m1_subset_1(X4,u1_struct_0(X1))
           => ~ ( r2_hidden(X4,X3)
                & ! [X5] :
                    ( ( v1_finset_1(X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                   => ~ ( r2_yellow_0(X1,X5)
                        & X4 = k2_yellow_0(X1,X5) ) ) ) )
        & ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_hidden(k2_yellow_0(X1,X4),X3) ) )
        & r2_yellow_0(X1,X2) ) ) ),
    introduced(definition)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( epred1_3(X2,X3,X1)
                 => k2_yellow_0(X1,X3) = k2_yellow_0(X1,X2) ) ) ) ) ),
    inference(apply_def,[status(thm)],[inference(assume_negation,[status(cth)],[t59_waybel_0]),c_0_4])).

fof(c_0_6,plain,(
    ! [X1,X3,X2] :
      ( epred1_3(X2,X3,X1)
     => ( ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_yellow_0(X1,X4) ) )
        & ! [X4] :
            ( m1_subset_1(X4,u1_struct_0(X1))
           => ~ ( r2_hidden(X4,X3)
                & ! [X5] :
                    ( ( v1_finset_1(X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X2)) )
                   => ~ ( r2_yellow_0(X1,X5)
                        & X4 = k2_yellow_0(X1,X5) ) ) ) )
        & ! [X4] :
            ( ( v1_finset_1(X4)
              & m1_subset_1(X4,k1_zfmisc_1(X2)) )
           => ( X4 != k1_xboole_0
             => r2_hidden(k2_yellow_0(X1,X4),X3) ) )
        & r2_yellow_0(X1,X2) ) ) ),
    inference(split_equiv,[status(thm)],[c_0_4])).

fof(c_0_7,plain,(
    ! [X13,X14,X15,X18,X20] :
      ( ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | v1_finset_1(esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | esk2_3(X13,X14,X15) != k1_xboole_0
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | m1_subset_1(esk3_3(X13,X14,X15),u1_struct_0(X13))
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | r2_hidden(esk3_3(X13,X14,X15),X15)
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | v1_finset_1(esk4_3(X13,X14,X15))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | m1_subset_1(esk4_3(X13,X14,X15),k1_zfmisc_1(X14))
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | esk4_3(X13,X14,X15) != k1_xboole_0
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X14,X20)
        | r1_lattice3(X13,X15,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) )
      & ( ~ r1_lattice3(X13,X15,X20)
        | r1_lattice3(X13,X14,X20)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r2_hidden(k2_yellow_0(X13,esk4_3(X13,X14,X15)),X15)
        | ~ v1_finset_1(X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(X14))
        | ~ r2_yellow_0(X13,X18)
        | esk3_3(X13,X14,X15) != k2_yellow_0(X13,X18)
        | ~ r2_yellow_0(X13,esk2_3(X13,X14,X15))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | v2_struct_0(X13)
        | ~ v3_orders_2(X13)
        | ~ v4_orders_2(X13)
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t57_waybel_0])])])])])])).

fof(c_0_8,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & epred1_3(esk6_0,esk7_0,esk5_0)
    & k2_yellow_0(esk5_0,esk7_0) != k2_yellow_0(esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_9,plain,(
    ! [X24,X25,X26,X27,X28,X30] :
      ( ( ~ v1_finset_1(X27)
        | ~ m1_subset_1(X27,k1_zfmisc_1(X26))
        | X27 = k1_xboole_0
        | r2_yellow_0(X24,X27)
        | ~ epred1_3(X26,X25,X24) )
      & ( v1_finset_1(esk8_4(X24,X25,X26,X28))
        | ~ r2_hidden(X28,X25)
        | ~ m1_subset_1(X28,u1_struct_0(X24))
        | ~ epred1_3(X26,X25,X24) )
      & ( m1_subset_1(esk8_4(X24,X25,X26,X28),k1_zfmisc_1(X26))
        | ~ r2_hidden(X28,X25)
        | ~ m1_subset_1(X28,u1_struct_0(X24))
        | ~ epred1_3(X26,X25,X24) )
      & ( r2_yellow_0(X24,esk8_4(X24,X25,X26,X28))
        | ~ r2_hidden(X28,X25)
        | ~ m1_subset_1(X28,u1_struct_0(X24))
        | ~ epred1_3(X26,X25,X24) )
      & ( X28 = k2_yellow_0(X24,esk8_4(X24,X25,X26,X28))
        | ~ r2_hidden(X28,X25)
        | ~ m1_subset_1(X28,u1_struct_0(X24))
        | ~ epred1_3(X26,X25,X24) )
      & ( ~ v1_finset_1(X30)
        | ~ m1_subset_1(X30,k1_zfmisc_1(X26))
        | X30 = k1_xboole_0
        | r2_hidden(k2_yellow_0(X24,X30),X25)
        | ~ epred1_3(X26,X25,X24) )
      & ( r2_yellow_0(X24,X26)
        | ~ epred1_3(X26,X25,X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])])).

cnf(c_0_10,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X4,X2))
    | r2_hidden(esk3_3(X1,X4,X2),X2)
    | m1_subset_1(esk2_3(X1,X4,X2),k1_zfmisc_1(X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_16,plain,(
    ! [X6,X7,X8] :
      ( ( m1_subset_1(esk1_3(X6,X7,X8),u1_struct_0(X6))
        | ~ r2_yellow_0(X6,X7)
        | k2_yellow_0(X6,X7) = k2_yellow_0(X6,X8)
        | v2_struct_0(X6)
        | ~ l1_orders_2(X6) )
      & ( ~ r1_lattice3(X6,X7,esk1_3(X6,X7,X8))
        | ~ r1_lattice3(X6,X8,esk1_3(X6,X7,X8))
        | ~ r2_yellow_0(X6,X7)
        | k2_yellow_0(X6,X7) = k2_yellow_0(X6,X8)
        | v2_struct_0(X6)
        | ~ l1_orders_2(X6) )
      & ( r1_lattice3(X6,X7,esk1_3(X6,X7,X8))
        | r1_lattice3(X6,X8,esk1_3(X6,X7,X8))
        | ~ r2_yellow_0(X6,X7)
        | k2_yellow_0(X6,X7) = k2_yellow_0(X6,X8)
        | v2_struct_0(X6)
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t49_yellow_0])])])])])])).

cnf(c_0_17,plain,
    ( r2_yellow_0(X1,X2)
    | ~ epred1_3(X2,X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( epred1_3(esk6_0,esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X4,X2),k1_zfmisc_1(X4))
    | m1_subset_1(esk3_3(X1,X4,X2),u1_struct_0(X1))
    | m1_subset_1(esk2_3(X1,X4,X2),k1_zfmisc_1(X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_20,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,X1))
    | r2_hidden(esk3_3(esk5_0,esk6_0,X1),X1)
    | r1_lattice3(esk5_0,esk6_0,X2)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,X1),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_10,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,plain,
    ( r1_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | r1_lattice3(X1,X3,esk1_3(X1,X2,X3))
    | k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( r2_yellow_0(esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,X2),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,X2),u1_struct_0(esk5_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,X2),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_25,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X2,X4))
    | r2_hidden(esk3_3(X1,X2,X4),X4)
    | m1_subset_1(esk2_3(X1,X2,X4),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_26,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( k2_yellow_0(esk5_0,esk6_0) = k2_yellow_0(esk5_0,X1)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,X1))
    | r1_lattice3(esk5_0,X1,esk1_3(esk5_0,esk6_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_14])]),c_0_15])).

cnf(c_0_28,negated_conjecture,
    ( k2_yellow_0(esk5_0,esk7_0) != k2_yellow_0(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),u1_struct_0(X1))
    | k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X2,X4),k1_zfmisc_1(X2))
    | m1_subset_1(esk3_3(X1,X2,X4),u1_struct_0(X1))
    | m1_subset_1(esk2_3(X1,X2,X4),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,X1,esk7_0))
    | r2_hidden(esk3_3(esk5_0,X1,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X2)
    | m1_subset_1(esk2_3(esk5_0,X1,esk7_0),k1_zfmisc_1(X1))
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_34,negated_conjecture,
    ( k2_yellow_0(esk5_0,esk6_0) = k2_yellow_0(esk5_0,X1)
    | m1_subset_1(esk1_3(esk5_0,esk6_0,X1),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_23]),c_0_14])]),c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk3_3(esk5_0,X2,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk4_3(esk5_0,X2,esk7_0),k1_zfmisc_1(X2))
    | m1_subset_1(esk2_3(esk5_0,X2,esk7_0),k1_zfmisc_1(X2))
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_36,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_27]),c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_11])).

cnf(c_0_38,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_34]),c_0_28])).

fof(c_0_41,plain,(
    ! [X10,X11,X12] :
      ( ~ r2_hidden(X10,X11)
      | ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | m1_subset_1(X10,X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_42,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_44,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_45,plain,
    ( k2_yellow_0(X1,X2) = k2_yellow_0(X1,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,esk1_3(X1,X2,X3))
    | ~ r1_lattice3(X1,X3,esk1_3(X1,X2,X3))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_34]),c_0_28])).

cnf(c_0_47,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_34]),c_0_28])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_21])).

cnf(c_0_49,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_38])).

cnf(c_0_50,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(k2_yellow_0(X3,X1),X4)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X2,X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_47]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_40])).

cnf(c_0_52,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_53,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk3_3(X1,X4,X2),u1_struct_0(X1))
    | m1_subset_1(esk2_3(X1,X4,X2),k1_zfmisc_1(X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X4,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_54,plain,
    ( esk4_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | r2_hidden(k2_yellow_0(X1,esk4_3(esk5_0,esk6_0,esk7_0)),X2)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ epred1_3(esk6_0,X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,X2),u1_struct_0(esk5_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,X2),k1_zfmisc_1(esk6_0))
    | esk4_3(esk5_0,esk6_0,X2) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_56,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X4,X2),k1_zfmisc_1(X4))
    | r2_hidden(esk3_3(X1,X4,X2),X2)
    | v1_finset_1(esk2_3(X1,X4,X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_57,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk3_3(X1,X2,X4),u1_struct_0(X1))
    | m1_subset_1(esk2_3(X1,X2,X4),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X2,X4) != k1_xboole_0
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_58,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk3_3(X1,X4,X2),u1_struct_0(X1))
    | m1_subset_1(esk2_3(X1,X4,X2),k1_zfmisc_1(X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X4,X2)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_59,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | r2_hidden(k2_yellow_0(esk5_0,esk4_3(esk5_0,esk6_0,esk7_0)),esk7_0)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_54,c_0_18])).

cnf(c_0_60,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_21])).

cnf(c_0_61,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,X1))
    | r2_hidden(esk3_3(esk5_0,esk6_0,X1),X1)
    | r1_lattice3(esk5_0,esk6_0,X2)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,X1),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_62,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk3_3(esk5_0,X2,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk2_3(esk5_0,X2,esk7_0),k1_zfmisc_1(X2))
    | esk4_3(esk5_0,X2,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_63,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_12]),c_0_13]),c_0_11]),c_0_21]),c_0_14])]),c_0_15]),c_0_60])).

cnf(c_0_64,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X2,X4),k1_zfmisc_1(X2))
    | r2_hidden(esk3_3(X1,X2,X4),X4)
    | v1_finset_1(esk2_3(X1,X2,X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_65,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_61,c_0_21])).

cnf(c_0_66,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk3_3(X1,X2,X4),u1_struct_0(X1))
    | m1_subset_1(esk2_3(X1,X2,X4),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X2,X4)),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_67,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_11])).

cnf(c_0_68,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_27]),c_0_28])).

cnf(c_0_69,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,X1,esk7_0))
    | r2_hidden(esk3_3(esk5_0,X1,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X2)
    | m1_subset_1(esk4_3(esk5_0,X1,esk7_0),k1_zfmisc_1(X1))
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_70,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_27]),c_0_28])).

cnf(c_0_71,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_59]),c_0_12]),c_0_13]),c_0_21]),c_0_11]),c_0_14])]),c_0_15]),c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_34]),c_0_28])).

cnf(c_0_73,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_11])).

cnf(c_0_74,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_34]),c_0_28])).

cnf(c_0_75,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_76,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_34]),c_0_28])).

cnf(c_0_78,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_34]),c_0_28])).

cnf(c_0_79,plain,
    ( X1 = k1_xboole_0
    | r2_yellow_0(X3,X1)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ epred1_3(X2,X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_80,negated_conjecture,
    ( m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_77]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_72])).

cnf(c_0_81,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_78]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_74])).

cnf(c_0_82,plain,
    ( esk2_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | r2_yellow_0(X1,esk2_3(esk5_0,esk6_0,esk7_0))
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_81])).

cnf(c_0_84,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X4,X2),k1_zfmisc_1(X4))
    | m1_subset_1(esk3_3(X1,X4,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk2_3(X1,X4,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_85,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X4,X2),k1_zfmisc_1(X4))
    | m1_subset_1(esk3_3(X1,X4,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,esk2_3(X1,X4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_86,negated_conjecture,
    ( esk2_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | r2_yellow_0(X1,esk2_3(esk5_0,esk6_0,esk7_0))
    | ~ epred1_3(esk6_0,X2,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,X2),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,X2),u1_struct_0(esk5_0))
    | esk2_3(esk5_0,esk6_0,X2) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_88,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X4,X2))
    | r2_hidden(esk3_3(X1,X4,X2),X2)
    | v1_finset_1(esk2_3(X1,X4,X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_89,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X2,X4),k1_zfmisc_1(X2))
    | m1_subset_1(esk3_3(X1,X2,X4),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk2_3(X1,X2,X4) != k1_xboole_0
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_90,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,X2),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,X2),u1_struct_0(esk5_0))
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_91,negated_conjecture,
    ( esk2_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_18])).

cnf(c_0_92,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_21])).

cnf(c_0_93,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,X1))
    | v1_finset_1(esk2_3(esk5_0,esk6_0,X1))
    | r2_hidden(esk3_3(esk5_0,esk6_0,X1),X1)
    | r1_lattice3(esk5_0,esk6_0,X2)
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_94,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X2,X4),k1_zfmisc_1(X2))
    | m1_subset_1(esk3_3(X1,X2,X4),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,esk2_3(X1,X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_95,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk3_3(esk5_0,X2,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk4_3(esk5_0,X2,esk7_0),k1_zfmisc_1(X2))
    | esk2_3(esk5_0,X2,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_96,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_91]),c_0_21])]),c_0_92])).

cnf(c_0_97,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X2,X4))
    | r2_hidden(esk3_3(X1,X2,X4),X4)
    | v1_finset_1(esk2_3(X1,X2,X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_98,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_21])).

cnf(c_0_99,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk3_3(esk5_0,X2,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk4_3(esk5_0,X2,esk7_0),k1_zfmisc_1(X2))
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,X2,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_100,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_11])).

cnf(c_0_101,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_27]),c_0_28])).

cnf(c_0_102,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,X1,esk7_0))
    | v1_finset_1(esk2_3(esk5_0,X1,esk7_0))
    | r2_hidden(esk3_3(esk5_0,X1,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X2)
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_103,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_27]),c_0_28])).

cnf(c_0_104,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_91]),c_0_11])]),c_0_100])).

cnf(c_0_105,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_34]),c_0_28])).

cnf(c_0_106,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_102,c_0_11])).

cnf(c_0_107,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_34]),c_0_28])).

cnf(c_0_108,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_109,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_106,c_0_107])).

cnf(c_0_110,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_34]),c_0_28])).

cnf(c_0_111,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_109,c_0_34]),c_0_28])).

cnf(c_0_112,negated_conjecture,
    ( m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_110]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_105])).

cnf(c_0_113,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_111]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_107])).

cnf(c_0_114,plain,
    ( esk4_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | r2_hidden(k2_yellow_0(X1,esk4_3(esk5_0,esk6_0,esk7_0)),X2)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_112])).

cnf(c_0_115,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_113])).

cnf(c_0_116,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk3_3(X1,X4,X2),u1_struct_0(X1))
    | v1_finset_1(esk2_3(X1,X4,X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X4,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_117,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(k2_yellow_0(X1,esk4_3(esk5_0,esk6_0,esk7_0)),X2)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ epred1_3(esk6_0,X2,X1) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_118,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,X1))
    | r1_lattice3(esk5_0,esk6_0,X2)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,X1),u1_struct_0(esk5_0))
    | esk4_3(esk5_0,esk6_0,X1) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_119,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk3_3(X1,X2,X4),u1_struct_0(X1))
    | v1_finset_1(esk2_3(X1,X2,X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X2,X4) != k1_xboole_0
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_120,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk3_3(X1,X4,X2),u1_struct_0(X1))
    | v1_finset_1(esk2_3(X1,X4,X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X4,X2)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_121,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(k2_yellow_0(esk5_0,esk4_3(esk5_0,esk6_0,esk7_0)),esk7_0)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_117,c_0_18])).

cnf(c_0_122,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_21])).

cnf(c_0_123,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,X1,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X2)
    | m1_subset_1(esk3_3(esk5_0,X1,esk7_0),u1_struct_0(esk5_0))
    | esk4_3(esk5_0,X1,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_124,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_120,c_0_121]),c_0_12]),c_0_13]),c_0_11]),c_0_21]),c_0_14])]),c_0_15]),c_0_122])).

cnf(c_0_125,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk3_3(X1,X2,X4),u1_struct_0(X1))
    | v1_finset_1(esk2_3(X1,X2,X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X2,X4)),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_126,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_123,c_0_11])).

cnf(c_0_127,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_27]),c_0_28])).

cnf(c_0_128,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_125,c_0_121]),c_0_12]),c_0_13]),c_0_21]),c_0_11]),c_0_14])]),c_0_15]),c_0_126])).

cnf(c_0_129,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_127,c_0_34]),c_0_28])).

cnf(c_0_130,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_128,c_0_129])).

cnf(c_0_131,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_130,c_0_34]),c_0_28])).

cnf(c_0_132,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_131]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_129])).

cnf(c_0_133,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X4,X2))
    | m1_subset_1(esk3_3(X1,X4,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk2_3(X1,X4,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_134,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X4,X2))
    | m1_subset_1(esk3_3(X1,X4,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,esk2_3(X1,X4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_135,plain,
    ( esk2_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | r2_yellow_0(X1,esk2_3(esk5_0,esk6_0,esk7_0))
    | ~ epred1_3(esk6_0,X2,X1) ),
    inference(spm,[status(thm)],[c_0_82,c_0_132])).

cnf(c_0_136,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,X1))
    | r1_lattice3(esk5_0,esk6_0,X2)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,X1),u1_struct_0(esk5_0))
    | esk2_3(esk5_0,esk6_0,X1) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_137,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X2,X4))
    | m1_subset_1(esk3_3(X1,X2,X4),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk2_3(X1,X2,X4) != k1_xboole_0
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_138,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,X1))
    | r1_lattice3(esk5_0,esk6_0,X2)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,X1),u1_struct_0(esk5_0))
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_139,negated_conjecture,
    ( esk2_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_135,c_0_18])).

cnf(c_0_140,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_136,c_0_21])).

cnf(c_0_141,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X2,X4))
    | m1_subset_1(esk3_3(X1,X2,X4),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,esk2_3(X1,X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_142,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,X1,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X2)
    | m1_subset_1(esk3_3(esk5_0,X1,esk7_0),u1_struct_0(esk5_0))
    | esk2_3(esk5_0,X1,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_143,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_138,c_0_139]),c_0_21])]),c_0_140])).

cnf(c_0_144,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,X1,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X2)
    | m1_subset_1(esk3_3(esk5_0,X1,esk7_0),u1_struct_0(esk5_0))
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,X1,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_145,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_142,c_0_11])).

cnf(c_0_146,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_143,c_0_27]),c_0_28])).

cnf(c_0_147,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_144,c_0_139]),c_0_11])]),c_0_145])).

cnf(c_0_148,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_34]),c_0_28])).

cnf(c_0_149,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_147,c_0_148])).

cnf(c_0_150,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_149,c_0_34]),c_0_28])).

cnf(c_0_151,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk3_3(X1,X4,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X4,X2) != k1_xboole_0
    | esk2_3(X1,X4,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_152,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_150]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_148])).

cnf(c_0_153,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk3_3(X1,X4,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X4,X2) != k1_xboole_0
    | ~ r2_yellow_0(X1,esk2_3(X1,X4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_154,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,X2),u1_struct_0(esk5_0))
    | esk2_3(esk5_0,esk6_0,X2) != k1_xboole_0
    | esk4_3(esk5_0,esk6_0,X2) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_151,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_155,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk3_3(X1,X2,X4),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X2,X4) != k1_xboole_0
    | esk2_3(X1,X2,X4) != k1_xboole_0
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_156,plain,
    ( esk4_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | r2_hidden(k2_yellow_0(X1,esk4_3(esk5_0,esk6_0,esk7_0)),X2)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ epred1_3(esk6_0,X2,X1) ),
    inference(spm,[status(thm)],[c_0_114,c_0_152])).

cnf(c_0_157,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,X2),u1_struct_0(esk5_0))
    | esk4_3(esk5_0,esk6_0,X2) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,X2)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_158,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_154,c_0_21])).

cnf(c_0_159,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X4,X2),k1_zfmisc_1(X4))
    | m1_subset_1(esk2_3(X1,X4,X2),k1_zfmisc_1(X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X4,X2) != k2_yellow_0(X1,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_160,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk3_3(X1,X2,X4),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X2,X4) != k1_xboole_0
    | ~ r2_yellow_0(X1,esk2_3(X1,X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_161,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk3_3(esk5_0,X2,esk7_0),u1_struct_0(esk5_0))
    | esk2_3(esk5_0,X2,esk7_0) != k1_xboole_0
    | esk4_3(esk5_0,X2,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_155,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_162,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk3_3(X1,X4,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X4,X2)),X2)
    | ~ r2_yellow_0(X1,esk2_3(X1,X4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_163,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | r2_hidden(k2_yellow_0(esk5_0,esk4_3(esk5_0,esk6_0,esk7_0)),esk7_0)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_156,c_0_18])).

cnf(c_0_164,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_139]),c_0_21])]),c_0_158])).

cnf(c_0_165,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk3_3(X1,X4,X2),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X4,X2)),X2)
    | esk2_3(X1,X4,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_166,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X4,X2),k1_zfmisc_1(X4))
    | r2_hidden(esk3_3(X1,X4,X2),X2)
    | m1_subset_1(esk2_3(X1,X4,X2),k1_zfmisc_1(X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_167,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X4,X2))
    | m1_subset_1(esk2_3(X1,X4,X2),k1_zfmisc_1(X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X4,X2) != k2_yellow_0(X1,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_168,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,X2),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,X2),k1_zfmisc_1(esk6_0))
    | esk3_3(esk5_0,esk6_0,X2) != k2_yellow_0(esk5_0,X3)
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_159,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_169,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk3_3(esk5_0,X2,esk7_0),u1_struct_0(esk5_0))
    | esk4_3(esk5_0,X2,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,X2,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_160,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_170,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_161,c_0_11])).

cnf(c_0_171,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_162,c_0_163]),c_0_12]),c_0_13]),c_0_11]),c_0_21]),c_0_14])]),c_0_15]),c_0_164])).

cnf(c_0_172,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_165,c_0_163]),c_0_12]),c_0_13]),c_0_11]),c_0_21]),c_0_14])]),c_0_15]),c_0_164])).

cnf(c_0_173,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,X1),X1)
    | r1_lattice3(esk5_0,esk6_0,X2)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,X1),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,X1),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_174,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,X1))
    | r1_lattice3(esk5_0,esk6_0,X2)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,X1),k1_zfmisc_1(esk6_0))
    | esk3_3(esk5_0,esk6_0,X1) != k2_yellow_0(esk5_0,X3)
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_167,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_175,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_168,c_0_21])).

cnf(c_0_176,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk3_3(X1,X2,X4),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X2,X4)),X4)
    | ~ r2_yellow_0(X1,esk2_3(X1,X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_177,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_139]),c_0_11])]),c_0_170])).

cnf(c_0_178,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk3_3(X1,X2,X4),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X2,X4)),X4)
    | esk2_3(X1,X2,X4) != k1_xboole_0
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_179,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_171,c_0_139]),c_0_172])).

cnf(c_0_180,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X2,X4),k1_zfmisc_1(X2))
    | r2_hidden(esk3_3(X1,X2,X4),X4)
    | m1_subset_1(esk2_3(X1,X2,X4),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_181,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_173,c_0_21])).

cnf(c_0_182,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_174,c_0_21])).

cnf(c_0_183,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_175,c_0_27]),c_0_28])).

cnf(c_0_184,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_176,c_0_163]),c_0_12]),c_0_13]),c_0_21]),c_0_11]),c_0_14])]),c_0_15]),c_0_177])).

cnf(c_0_185,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_178,c_0_163]),c_0_12]),c_0_13]),c_0_21]),c_0_11]),c_0_14])]),c_0_15]),c_0_177])).

cnf(c_0_186,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_179,c_0_27]),c_0_28])).

cnf(c_0_187,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,X1,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X2)
    | m1_subset_1(esk4_3(esk5_0,X1,esk7_0),k1_zfmisc_1(X1))
    | m1_subset_1(esk2_3(esk5_0,X1,esk7_0),k1_zfmisc_1(X1))
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_180,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_188,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_181,c_0_27]),c_0_28])).

cnf(c_0_189,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_182,c_0_27]),c_0_28])).

cnf(c_0_190,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_183,c_0_34]),c_0_28])).

cnf(c_0_191,plain,
    ( m1_subset_1(esk8_4(X1,X2,X3,X4),k1_zfmisc_1(X3))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_192,plain,
    ( v1_finset_1(esk8_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_193,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_184,c_0_139]),c_0_185])).

cnf(c_0_194,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_186,c_0_34]),c_0_28])).

cnf(c_0_195,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_187,c_0_11])).

cnf(c_0_196,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_188,c_0_34]),c_0_28])).

cnf(c_0_197,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_189,c_0_34]),c_0_28])).

cnf(c_0_198,plain,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_190,c_0_191]),c_0_192])).

cnf(c_0_199,plain,
    ( r2_yellow_0(X1,esk8_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ epred1_3(X3,X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_200,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_193,c_0_194])).

cnf(c_0_201,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_195,c_0_196])).

cnf(c_0_202,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_197,c_0_191]),c_0_192])).

cnf(c_0_203,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X2,X4),k1_zfmisc_1(X2))
    | m1_subset_1(esk2_3(X1,X2,X4),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X2,X4) != k2_yellow_0(X1,X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_204,plain,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_198,c_0_199])).

cnf(c_0_205,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_200,c_0_34]),c_0_28])).

cnf(c_0_206,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_201,c_0_34]),c_0_28])).

cnf(c_0_207,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X2,X4))
    | m1_subset_1(esk2_3(X1,X2,X4),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X2,X4) != k2_yellow_0(X1,X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_208,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_202,c_0_199])).

cnf(c_0_209,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk4_3(esk5_0,X2,esk7_0),k1_zfmisc_1(X2))
    | m1_subset_1(esk2_3(esk5_0,X2,esk7_0),k1_zfmisc_1(X2))
    | esk3_3(esk5_0,X2,esk7_0) != k2_yellow_0(esk5_0,X3)
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_203,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_210,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,X1)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_204,c_0_18]),c_0_48])).

cnf(c_0_211,plain,
    ( X1 = k2_yellow_0(X2,esk8_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ epred1_3(X4,X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_212,negated_conjecture,
    ( m1_subset_1(esk3_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_205]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_194])).

cnf(c_0_213,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_206]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_196])).

cnf(c_0_214,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,X1,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X2)
    | m1_subset_1(esk2_3(esk5_0,X1,esk7_0),k1_zfmisc_1(X1))
    | esk3_3(esk5_0,X1,esk7_0) != k2_yellow_0(esk5_0,X3)
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_207,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_215,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,X1)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_208,c_0_18]),c_0_48])).

cnf(c_0_216,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_209,c_0_11])).

cnf(c_0_217,plain,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_210,c_0_211]),c_0_18])])]),c_0_212])]),c_0_213])).

cnf(c_0_218,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_214,c_0_11])).

cnf(c_0_219,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_215,c_0_211]),c_0_18])])]),c_0_212])]),c_0_49])).

cnf(c_0_220,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_216,c_0_217])).

cnf(c_0_221,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_218,c_0_219])).

cnf(c_0_222,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_220,c_0_34]),c_0_28])).

cnf(c_0_223,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_221,c_0_34]),c_0_28])).

cnf(c_0_224,plain,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_222,c_0_191]),c_0_192])).

cnf(c_0_225,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_223,c_0_191]),c_0_192])).

cnf(c_0_226,plain,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_224,c_0_199])).

cnf(c_0_227,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_225,c_0_199])).

cnf(c_0_228,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,X1)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_226,c_0_18]),c_0_48])).

cnf(c_0_229,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,X1)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_227,c_0_18]),c_0_48])).

cnf(c_0_230,plain,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_228,c_0_211]),c_0_18])])]),c_0_212])]),c_0_213])).

cnf(c_0_231,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_229,c_0_211]),c_0_18])])]),c_0_212])]),c_0_49])).

cnf(c_0_232,plain,
    ( m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_230]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_217])).

cnf(c_0_233,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_231]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_219])).

cnf(c_0_234,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk2_3(X1,X4,X2),k1_zfmisc_1(X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X4,X2) != k1_xboole_0
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X4,X2) != k2_yellow_0(X1,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_235,plain,
    ( r1_lattice3(X1,X4,X3)
    | r2_hidden(esk3_3(X1,X4,X2),X2)
    | m1_subset_1(esk2_3(X1,X4,X2),k1_zfmisc_1(X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X4,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_236,plain,
    ( esk4_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | r2_hidden(k2_yellow_0(X1,esk4_3(esk5_0,esk6_0,esk7_0)),X2)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ epred1_3(esk6_0,X2,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_232]),c_0_233])).

cnf(c_0_237,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,X2),k1_zfmisc_1(esk6_0))
    | esk3_3(esk5_0,esk6_0,X2) != k2_yellow_0(esk5_0,X3)
    | esk4_3(esk5_0,esk6_0,X2) != k1_xboole_0
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_234,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_238,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,X1),X1)
    | r1_lattice3(esk5_0,esk6_0,X2)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,X1),k1_zfmisc_1(esk6_0))
    | esk4_3(esk5_0,esk6_0,X1) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_235,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_239,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk2_3(X1,X4,X2),k1_zfmisc_1(X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X4,X2)),X2)
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X4,X2) != k2_yellow_0(X1,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_240,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | r2_hidden(k2_yellow_0(esk5_0,esk4_3(esk5_0,esk6_0,esk7_0)),esk7_0)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_236,c_0_18])).

cnf(c_0_241,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_237,c_0_21])).

cnf(c_0_242,plain,
    ( r1_lattice3(X1,X4,X3)
    | r2_hidden(esk3_3(X1,X2,X4),X4)
    | m1_subset_1(esk2_3(X1,X2,X4),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X2,X4) != k1_xboole_0
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_243,plain,
    ( r1_lattice3(X1,X4,X3)
    | r2_hidden(esk3_3(X1,X4,X2),X2)
    | m1_subset_1(esk2_3(X1,X4,X2),k1_zfmisc_1(X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X4,X2)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_244,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_238,c_0_21])).

cnf(c_0_245,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X4,X2),k1_zfmisc_1(X4))
    | v1_finset_1(esk2_3(X1,X4,X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X4,X2) != k2_yellow_0(X1,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_246,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_239,c_0_240]),c_0_12]),c_0_13]),c_0_11]),c_0_21]),c_0_14])]),c_0_15]),c_0_241])).

cnf(c_0_247,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,X1,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X2)
    | m1_subset_1(esk2_3(esk5_0,X1,esk7_0),k1_zfmisc_1(X1))
    | esk4_3(esk5_0,X1,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_242,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_248,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_243,c_0_240]),c_0_12]),c_0_13]),c_0_11]),c_0_21]),c_0_14])]),c_0_15]),c_0_244])).

cnf(c_0_249,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,X1))
    | r1_lattice3(esk5_0,esk6_0,X2)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,X1),k1_zfmisc_1(esk6_0))
    | esk3_3(esk5_0,esk6_0,X1) != k2_yellow_0(esk5_0,X3)
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_245,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_250,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_246,c_0_27]),c_0_28])).

cnf(c_0_251,plain,
    ( r1_lattice3(X1,X4,X3)
    | r2_hidden(esk3_3(X1,X2,X4),X4)
    | m1_subset_1(esk2_3(X1,X2,X4),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X2,X4)),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_252,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_247,c_0_11])).

cnf(c_0_253,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_248,c_0_27]),c_0_28])).

cnf(c_0_254,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_249,c_0_21])).

cnf(c_0_255,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_250,c_0_34]),c_0_28])).

cnf(c_0_256,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_251,c_0_240]),c_0_12]),c_0_13]),c_0_21]),c_0_11]),c_0_14])]),c_0_15]),c_0_252])).

cnf(c_0_257,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_253,c_0_34]),c_0_28])).

cnf(c_0_258,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_254,c_0_27]),c_0_28])).

cnf(c_0_259,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk2_3(X1,X2,X4),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X2,X4) != k1_xboole_0
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X2,X4) != k2_yellow_0(X1,X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_260,plain,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_255,c_0_191]),c_0_192])).

cnf(c_0_261,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_256,c_0_257])).

cnf(c_0_262,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_258,c_0_34]),c_0_28])).

cnf(c_0_263,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk2_3(esk5_0,X2,esk7_0),k1_zfmisc_1(X2))
    | esk3_3(esk5_0,X2,esk7_0) != k2_yellow_0(esk5_0,X3)
    | esk4_3(esk5_0,X2,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_259,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_264,plain,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_260,c_0_199])).

cnf(c_0_265,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_261,c_0_34]),c_0_28])).

cnf(c_0_266,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_262,c_0_191]),c_0_192])).

cnf(c_0_267,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk2_3(X1,X2,X4),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X2,X4)),X4)
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X2,X4) != k2_yellow_0(X1,X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_268,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_263,c_0_11])).

cnf(c_0_269,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,X1)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_264,c_0_18]),c_0_48])).

cnf(c_0_270,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_265]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_257])).

cnf(c_0_271,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X2,X4),k1_zfmisc_1(X2))
    | v1_finset_1(esk2_3(X1,X2,X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X2,X4) != k2_yellow_0(X1,X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_272,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_266,c_0_199])).

cnf(c_0_273,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_267,c_0_240]),c_0_12]),c_0_13]),c_0_21]),c_0_11]),c_0_14])]),c_0_15]),c_0_268])).

cnf(c_0_274,plain,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_269,c_0_211]),c_0_18])])]),c_0_212])]),c_0_270])).

cnf(c_0_275,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,X1,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X2)
    | m1_subset_1(esk4_3(esk5_0,X1,esk7_0),k1_zfmisc_1(X1))
    | esk3_3(esk5_0,X1,esk7_0) != k2_yellow_0(esk5_0,X3)
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_271,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_276,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,X1)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_272,c_0_18]),c_0_48])).

cnf(c_0_277,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_273,c_0_274])).

cnf(c_0_278,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_275,c_0_11])).

cnf(c_0_279,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_276,c_0_211]),c_0_18])])]),c_0_212])]),c_0_81])).

cnf(c_0_280,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_277,c_0_34]),c_0_28])).

cnf(c_0_281,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_278,c_0_279])).

cnf(c_0_282,plain,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_280,c_0_191]),c_0_192])).

cnf(c_0_283,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_281,c_0_34]),c_0_28])).

cnf(c_0_284,plain,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_282,c_0_199])).

cnf(c_0_285,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_283,c_0_191]),c_0_192])).

cnf(c_0_286,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,X1)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_284,c_0_18]),c_0_48])).

cnf(c_0_287,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_285,c_0_199])).

cnf(c_0_288,plain,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_286,c_0_211]),c_0_18])])]),c_0_212])]),c_0_270])).

cnf(c_0_289,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,X1)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_287,c_0_18]),c_0_48])).

cnf(c_0_290,plain,
    ( m1_subset_1(esk2_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_288]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_274])).

cnf(c_0_291,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_289,c_0_211]),c_0_18])])]),c_0_212])]),c_0_81])).

cnf(c_0_292,plain,
    ( esk2_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | r2_yellow_0(X1,esk2_3(esk5_0,esk6_0,esk7_0))
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_290])).

cnf(c_0_293,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_291]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_279])).

cnf(c_0_294,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X4,X2),k1_zfmisc_1(X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X4,X2) != k2_yellow_0(X1,X5)
    | esk2_3(X1,X4,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_295,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X4,X2),k1_zfmisc_1(X4))
    | r2_hidden(esk3_3(X1,X4,X2),X2)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk2_3(X1,X4,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_296,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X4,X2),k1_zfmisc_1(X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X4,X2) != k2_yellow_0(X1,X5)
    | ~ r2_yellow_0(X1,esk2_3(X1,X4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_297,plain,
    ( esk2_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | r2_yellow_0(X1,esk2_3(esk5_0,esk6_0,esk7_0))
    | ~ epred1_3(esk6_0,X2,X1) ),
    inference(spm,[status(thm)],[c_0_292,c_0_293])).

cnf(c_0_298,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,X2),k1_zfmisc_1(esk6_0))
    | esk3_3(esk5_0,esk6_0,X2) != k2_yellow_0(esk5_0,X3)
    | esk2_3(esk5_0,esk6_0,X2) != k1_xboole_0
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_294,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_299,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X4,X2),k1_zfmisc_1(X4))
    | r2_hidden(esk3_3(X1,X4,X2),X2)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,esk2_3(X1,X4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_300,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,X1),X1)
    | r1_lattice3(esk5_0,esk6_0,X2)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,X1),k1_zfmisc_1(esk6_0))
    | esk2_3(esk5_0,esk6_0,X1) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_295,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_301,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,X2),k1_zfmisc_1(esk6_0))
    | esk3_3(esk5_0,esk6_0,X2) != k2_yellow_0(esk5_0,X3)
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,X2))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_296,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_302,negated_conjecture,
    ( esk2_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_297,c_0_18])).

cnf(c_0_303,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_298,c_0_21])).

cnf(c_0_304,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X2,X4),k1_zfmisc_1(X2))
    | r2_hidden(esk3_3(X1,X2,X4),X4)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk2_3(X1,X2,X4) != k1_xboole_0
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_305,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,X1),X1)
    | r1_lattice3(esk5_0,esk6_0,X2)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,X1),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_299,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_306,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_300,c_0_21])).

cnf(c_0_307,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X4,X2))
    | v1_finset_1(esk2_3(X1,X4,X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X4,X2) != k2_yellow_0(X1,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_308,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_301,c_0_302]),c_0_21])]),c_0_303])).

cnf(c_0_309,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X2,X4),k1_zfmisc_1(X2))
    | r2_hidden(esk3_3(X1,X2,X4),X4)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,esk2_3(X1,X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_310,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,X1,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X2)
    | m1_subset_1(esk4_3(esk5_0,X1,esk7_0),k1_zfmisc_1(X1))
    | esk2_3(esk5_0,X1,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_304,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_311,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_305,c_0_302]),c_0_21])]),c_0_306])).

cnf(c_0_312,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,X1))
    | v1_finset_1(esk2_3(esk5_0,esk6_0,X1))
    | r1_lattice3(esk5_0,esk6_0,X2)
    | esk3_3(esk5_0,esk6_0,X1) != k2_yellow_0(esk5_0,X3)
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_307,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_313,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_308,c_0_27]),c_0_28])).

cnf(c_0_314,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,X1,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X2)
    | m1_subset_1(esk4_3(esk5_0,X1,esk7_0),k1_zfmisc_1(X1))
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,X1,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_309,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_315,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_310,c_0_11])).

cnf(c_0_316,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_311,c_0_27]),c_0_28])).

cnf(c_0_317,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_312,c_0_21])).

cnf(c_0_318,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_313,c_0_34]),c_0_28])).

cnf(c_0_319,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_314,c_0_302]),c_0_11])]),c_0_315])).

cnf(c_0_320,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_316,c_0_34]),c_0_28])).

cnf(c_0_321,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_317,c_0_27]),c_0_28])).

cnf(c_0_322,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X2,X4),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X2,X4) != k2_yellow_0(X1,X5)
    | esk2_3(X1,X2,X4) != k1_xboole_0
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_323,plain,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_318,c_0_191]),c_0_192])).

cnf(c_0_324,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_319,c_0_320])).

cnf(c_0_325,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_321,c_0_34]),c_0_28])).

cnf(c_0_326,plain,
    ( r1_lattice3(X1,X4,X3)
    | m1_subset_1(esk4_3(X1,X2,X4),k1_zfmisc_1(X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X2,X4) != k2_yellow_0(X1,X5)
    | ~ r2_yellow_0(X1,esk2_3(X1,X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_327,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk4_3(esk5_0,X2,esk7_0),k1_zfmisc_1(X2))
    | esk3_3(esk5_0,X2,esk7_0) != k2_yellow_0(esk5_0,X3)
    | esk2_3(esk5_0,X2,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_322,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_328,plain,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_323,c_0_199])).

cnf(c_0_329,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_324,c_0_34]),c_0_28])).

cnf(c_0_330,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_325,c_0_191]),c_0_192])).

cnf(c_0_331,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk4_3(esk5_0,X2,esk7_0),k1_zfmisc_1(X2))
    | esk3_3(esk5_0,X2,esk7_0) != k2_yellow_0(esk5_0,X3)
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,X2,esk7_0))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_326,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_332,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_327,c_0_11])).

cnf(c_0_333,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,X1)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_328,c_0_18]),c_0_48])).

cnf(c_0_334,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_329]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_320])).

cnf(c_0_335,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X2,X4))
    | v1_finset_1(esk2_3(X1,X2,X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X2,X4) != k2_yellow_0(X1,X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_336,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_330,c_0_199])).

cnf(c_0_337,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_331,c_0_302]),c_0_11])]),c_0_332])).

cnf(c_0_338,plain,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_333,c_0_211]),c_0_18])])]),c_0_212])]),c_0_334])).

cnf(c_0_339,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,X1,esk7_0))
    | v1_finset_1(esk2_3(esk5_0,X1,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X2)
    | esk3_3(esk5_0,X1,esk7_0) != k2_yellow_0(esk5_0,X3)
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_335,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_340,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,X1)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_336,c_0_18]),c_0_48])).

cnf(c_0_341,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_337,c_0_338])).

cnf(c_0_342,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_339,c_0_11])).

cnf(c_0_343,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_340,c_0_211]),c_0_18])])]),c_0_212])]),c_0_113])).

cnf(c_0_344,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_341,c_0_34]),c_0_28])).

cnf(c_0_345,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_342,c_0_343])).

cnf(c_0_346,plain,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_344,c_0_191]),c_0_192])).

cnf(c_0_347,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_345,c_0_34]),c_0_28])).

cnf(c_0_348,plain,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_346,c_0_199])).

cnf(c_0_349,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_347,c_0_191]),c_0_192])).

cnf(c_0_350,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,X1)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_348,c_0_18]),c_0_48])).

cnf(c_0_351,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_349,c_0_199])).

cnf(c_0_352,plain,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_350,c_0_211]),c_0_18])])]),c_0_212])]),c_0_334])).

cnf(c_0_353,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,X1)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_351,c_0_18]),c_0_48])).

cnf(c_0_354,plain,
    ( m1_subset_1(esk4_3(esk5_0,esk6_0,esk7_0),k1_zfmisc_1(esk6_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_352]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_338])).

cnf(c_0_355,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_353,c_0_211]),c_0_18])])]),c_0_212])]),c_0_113])).

cnf(c_0_356,plain,
    ( esk4_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | r2_hidden(k2_yellow_0(X1,esk4_3(esk5_0,esk6_0,esk7_0)),X2)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_354])).

cnf(c_0_357,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_355]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_343])).

cnf(c_0_358,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk2_3(X1,X4,X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X4,X2) != k1_xboole_0
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X4,X2) != k2_yellow_0(X1,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_359,plain,
    ( r1_lattice3(X1,X4,X3)
    | r2_hidden(esk3_3(X1,X4,X2),X2)
    | v1_finset_1(esk2_3(X1,X4,X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X4,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_360,plain,
    ( esk4_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(k2_yellow_0(X1,esk4_3(esk5_0,esk6_0,esk7_0)),X2)
    | ~ epred1_3(esk6_0,X2,X1) ),
    inference(spm,[status(thm)],[c_0_356,c_0_357])).

cnf(c_0_361,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,X1))
    | r1_lattice3(esk5_0,esk6_0,X2)
    | esk3_3(esk5_0,esk6_0,X1) != k2_yellow_0(esk5_0,X3)
    | esk4_3(esk5_0,esk6_0,X1) != k1_xboole_0
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_358,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_362,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,X1))
    | r2_hidden(esk3_3(esk5_0,esk6_0,X1),X1)
    | r1_lattice3(esk5_0,esk6_0,X2)
    | esk4_3(esk5_0,esk6_0,X1) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_359,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_363,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk2_3(X1,X4,X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X4,X2)),X2)
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X4,X2) != k2_yellow_0(X1,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_364,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(k2_yellow_0(esk5_0,esk4_3(esk5_0,esk6_0,esk7_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_360,c_0_18])).

cnf(c_0_365,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_361,c_0_21])).

cnf(c_0_366,plain,
    ( r1_lattice3(X1,X4,X3)
    | r2_hidden(esk3_3(X1,X2,X4),X4)
    | v1_finset_1(esk2_3(X1,X2,X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X2,X4) != k1_xboole_0
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_367,plain,
    ( r1_lattice3(X1,X4,X3)
    | r2_hidden(esk3_3(X1,X4,X2),X2)
    | v1_finset_1(esk2_3(X1,X4,X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X4,X2)),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_368,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_362,c_0_21])).

cnf(c_0_369,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_363,c_0_364]),c_0_12]),c_0_13]),c_0_11]),c_0_21]),c_0_14])]),c_0_15]),c_0_365])).

cnf(c_0_370,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,X1,esk7_0))
    | r2_hidden(esk3_3(esk5_0,X1,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X2)
    | esk4_3(esk5_0,X1,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_366,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_371,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_367,c_0_364]),c_0_12]),c_0_13]),c_0_11]),c_0_21]),c_0_14])]),c_0_15]),c_0_368])).

cnf(c_0_372,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_369,c_0_27]),c_0_28])).

cnf(c_0_373,plain,
    ( r1_lattice3(X1,X4,X3)
    | r2_hidden(esk3_3(X1,X2,X4),X4)
    | v1_finset_1(esk2_3(X1,X2,X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X2,X4)),X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_374,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_370,c_0_11])).

cnf(c_0_375,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_371,c_0_27]),c_0_28])).

cnf(c_0_376,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_372,c_0_34]),c_0_28])).

cnf(c_0_377,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_373,c_0_364]),c_0_12]),c_0_13]),c_0_21]),c_0_11]),c_0_14])]),c_0_15]),c_0_374])).

cnf(c_0_378,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_375,c_0_34]),c_0_28])).

cnf(c_0_379,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk2_3(X1,X2,X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X2,X4) != k1_xboole_0
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X2,X4) != k2_yellow_0(X1,X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_380,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_376,c_0_191]),c_0_192])).

cnf(c_0_381,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_377,c_0_378])).

cnf(c_0_382,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,X1,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X2)
    | esk3_3(esk5_0,X1,esk7_0) != k2_yellow_0(esk5_0,X3)
    | esk4_3(esk5_0,X1,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_379,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_383,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_380,c_0_199])).

cnf(c_0_384,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_381,c_0_34]),c_0_28])).

cnf(c_0_385,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk2_3(X1,X2,X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X2,X4)),X4)
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X2,X4) != k2_yellow_0(X1,X5)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_386,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_382,c_0_11])).

cnf(c_0_387,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,X1)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_383,c_0_18]),c_0_48])).

cnf(c_0_388,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_384]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_378])).

cnf(c_0_389,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_385,c_0_364]),c_0_12]),c_0_13]),c_0_21]),c_0_11]),c_0_14])]),c_0_15]),c_0_386])).

cnf(c_0_390,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_387,c_0_211]),c_0_18])])]),c_0_212])]),c_0_388])).

cnf(c_0_391,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_389,c_0_390])).

cnf(c_0_392,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_391,c_0_34]),c_0_28])).

cnf(c_0_393,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_392,c_0_191]),c_0_192])).

cnf(c_0_394,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_393,c_0_199])).

cnf(c_0_395,negated_conjecture,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,X1)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_394,c_0_18]),c_0_48])).

cnf(c_0_396,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_395,c_0_211]),c_0_18])])]),c_0_212])]),c_0_388])).

cnf(c_0_397,plain,
    ( v1_finset_1(esk2_3(esk5_0,esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_396]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_390])).

cnf(c_0_398,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X4,X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X4,X2) != k2_yellow_0(X1,X5)
    | esk2_3(X1,X4,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_399,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X4,X2))
    | r2_hidden(esk3_3(X1,X4,X2),X2)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk2_3(X1,X4,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_400,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X4,X2))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X4,X2) != k2_yellow_0(X1,X5)
    | ~ r2_yellow_0(X1,esk2_3(X1,X4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_401,plain,
    ( esk2_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | r2_yellow_0(X1,esk2_3(esk5_0,esk6_0,esk7_0))
    | ~ epred1_3(esk6_0,X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_292,c_0_397])])).

cnf(c_0_402,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,X1))
    | r1_lattice3(esk5_0,esk6_0,X2)
    | esk3_3(esk5_0,esk6_0,X1) != k2_yellow_0(esk5_0,X3)
    | esk2_3(esk5_0,esk6_0,X1) != k1_xboole_0
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_398,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_403,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X4,X2))
    | r2_hidden(esk3_3(X1,X4,X2),X2)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,esk2_3(X1,X4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_404,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,X1))
    | r2_hidden(esk3_3(esk5_0,esk6_0,X1),X1)
    | r1_lattice3(esk5_0,esk6_0,X2)
    | esk2_3(esk5_0,esk6_0,X1) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_399,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_405,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,X1))
    | r1_lattice3(esk5_0,esk6_0,X2)
    | esk3_3(esk5_0,esk6_0,X1) != k2_yellow_0(esk5_0,X3)
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,X1))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_400,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_406,negated_conjecture,
    ( esk2_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,esk7_0)) ),
    inference(spm,[status(thm)],[c_0_401,c_0_18])).

cnf(c_0_407,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_402,c_0_21])).

cnf(c_0_408,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X2,X4))
    | r2_hidden(esk3_3(X1,X2,X4),X4)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk2_3(X1,X2,X4) != k1_xboole_0
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_409,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,X1))
    | r2_hidden(esk3_3(esk5_0,esk6_0,X1),X1)
    | r1_lattice3(esk5_0,esk6_0,X2)
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_403,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_410,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_404,c_0_21])).

cnf(c_0_411,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_405,c_0_406]),c_0_21])]),c_0_407])).

cnf(c_0_412,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X2,X4))
    | r2_hidden(esk3_3(X1,X2,X4),X4)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(X1,esk2_3(X1,X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_413,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,X1,esk7_0))
    | r2_hidden(esk3_3(esk5_0,X1,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X2)
    | esk2_3(esk5_0,X1,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_408,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_414,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_409,c_0_406]),c_0_21])]),c_0_410])).

cnf(c_0_415,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_411,c_0_27]),c_0_28])).

cnf(c_0_416,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,X1,esk7_0))
    | r2_hidden(esk3_3(esk5_0,X1,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X2)
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,X1,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_412,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_417,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_413,c_0_11])).

cnf(c_0_418,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_414,c_0_27]),c_0_28])).

cnf(c_0_419,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_415,c_0_34]),c_0_28])).

cnf(c_0_420,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_416,c_0_406]),c_0_11])]),c_0_417])).

cnf(c_0_421,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_418,c_0_34]),c_0_28])).

cnf(c_0_422,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X2,X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X2,X4) != k2_yellow_0(X1,X5)
    | esk2_3(X1,X2,X4) != k1_xboole_0
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_423,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_419,c_0_191]),c_0_192])).

cnf(c_0_424,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_420,c_0_421])).

cnf(c_0_425,plain,
    ( r1_lattice3(X1,X4,X3)
    | v1_finset_1(esk4_3(X1,X2,X4))
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X2,X4) != k2_yellow_0(X1,X5)
    | ~ r2_yellow_0(X1,esk2_3(X1,X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_426,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,X1,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X2)
    | esk3_3(esk5_0,X1,esk7_0) != k2_yellow_0(esk5_0,X3)
    | esk2_3(esk5_0,X1,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_422,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_427,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_423,c_0_199])).

cnf(c_0_428,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_424,c_0_34]),c_0_28])).

cnf(c_0_429,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,X1,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X2)
    | esk3_3(esk5_0,X1,esk7_0) != k2_yellow_0(esk5_0,X3)
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,X1,esk7_0))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_425,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_430,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_426,c_0_11])).

cnf(c_0_431,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,X1)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_427,c_0_18]),c_0_48])).

cnf(c_0_432,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_428]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_421])).

cnf(c_0_433,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_429,c_0_406]),c_0_11])]),c_0_430])).

cnf(c_0_434,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_431,c_0_211]),c_0_18])])]),c_0_212])]),c_0_432])).

cnf(c_0_435,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_433,c_0_434])).

cnf(c_0_436,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_435,c_0_34]),c_0_28])).

cnf(c_0_437,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_436,c_0_191]),c_0_192])).

cnf(c_0_438,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_437,c_0_199])).

cnf(c_0_439,negated_conjecture,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,X1)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_438,c_0_18]),c_0_48])).

cnf(c_0_440,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0))
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_439,c_0_211]),c_0_18])])]),c_0_212])]),c_0_432])).

cnf(c_0_441,plain,
    ( r1_lattice3(X1,X4,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X4,X2) != k1_xboole_0
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X4,X2) != k2_yellow_0(X1,X5)
    | esk2_3(X1,X4,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_442,plain,
    ( r1_lattice3(X1,X4,X3)
    | r2_hidden(esk3_3(X1,X4,X2),X2)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X4,X2) != k1_xboole_0
    | esk2_3(X1,X4,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_443,plain,
    ( v1_finset_1(esk4_3(esk5_0,esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_440]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_434])).

cnf(c_0_444,plain,
    ( r1_lattice3(X1,X4,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X4,X2) != k1_xboole_0
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X4,X2) != k2_yellow_0(X1,X5)
    | ~ r2_yellow_0(X1,esk2_3(X1,X4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_445,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | esk3_3(esk5_0,esk6_0,X2) != k2_yellow_0(esk5_0,X3)
    | esk2_3(esk5_0,esk6_0,X2) != k1_xboole_0
    | esk4_3(esk5_0,esk6_0,X2) != k1_xboole_0
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_441,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_446,plain,
    ( r1_lattice3(X1,X4,X3)
    | r2_hidden(esk3_3(X1,X4,X2),X2)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X4,X2) != k1_xboole_0
    | ~ r2_yellow_0(X1,esk2_3(X1,X4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_447,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,X1),X1)
    | r1_lattice3(esk5_0,esk6_0,X2)
    | esk2_3(esk5_0,esk6_0,X1) != k1_xboole_0
    | esk4_3(esk5_0,esk6_0,X1) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_442,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_448,plain,
    ( esk4_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | r2_hidden(k2_yellow_0(X1,esk4_3(esk5_0,esk6_0,esk7_0)),X2)
    | ~ epred1_3(esk6_0,X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_356,c_0_443])])).

cnf(c_0_449,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | esk3_3(esk5_0,esk6_0,X2) != k2_yellow_0(esk5_0,X3)
    | esk4_3(esk5_0,esk6_0,X2) != k1_xboole_0
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,X2))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_444,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_450,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_445,c_0_21])).

cnf(c_0_451,plain,
    ( r1_lattice3(X1,X4,X3)
    | r2_hidden(esk3_3(X1,X2,X4),X4)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X2,X4) != k1_xboole_0
    | esk2_3(X1,X2,X4) != k1_xboole_0
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_452,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,X1),X1)
    | r1_lattice3(esk5_0,esk6_0,X2)
    | esk4_3(esk5_0,esk6_0,X1) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_446,c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_453,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_447,c_0_21])).

cnf(c_0_454,plain,
    ( r1_lattice3(X1,X4,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X4,X2)),X2)
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X4,X2) != k2_yellow_0(X1,X5)
    | ~ r2_yellow_0(X1,esk2_3(X1,X4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_455,negated_conjecture,
    ( esk4_3(esk5_0,esk6_0,esk7_0) = k1_xboole_0
    | r2_hidden(k2_yellow_0(esk5_0,esk4_3(esk5_0,esk6_0,esk7_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_448,c_0_18])).

cnf(c_0_456,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_449,c_0_406]),c_0_21])]),c_0_450])).

cnf(c_0_457,plain,
    ( r1_lattice3(X1,X4,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X4,X2)),X2)
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X4,X2) != k2_yellow_0(X1,X5)
    | esk2_3(X1,X4,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_458,plain,
    ( r1_lattice3(X1,X4,X3)
    | r2_hidden(esk3_3(X1,X2,X4),X4)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X2,X4) != k1_xboole_0
    | ~ r2_yellow_0(X1,esk2_3(X1,X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_459,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,X1,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X2)
    | esk2_3(esk5_0,X1,esk7_0) != k1_xboole_0
    | esk4_3(esk5_0,X1,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_451,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_460,plain,
    ( r1_lattice3(X1,X4,X3)
    | r2_hidden(esk3_3(X1,X4,X2),X2)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X4,X2)),X2)
    | ~ r2_yellow_0(X1,esk2_3(X1,X4,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_461,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_452,c_0_406]),c_0_21])]),c_0_453])).

cnf(c_0_462,plain,
    ( r1_lattice3(X1,X4,X3)
    | r2_hidden(esk3_3(X1,X4,X2),X2)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X4,X2)),X2)
    | esk2_3(X1,X4,X2) != k1_xboole_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_463,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,esk7_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_454,c_0_455]),c_0_12]),c_0_13]),c_0_11]),c_0_21]),c_0_14])]),c_0_15]),c_0_456])).

cnf(c_0_464,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_457,c_0_455]),c_0_12]),c_0_13]),c_0_11]),c_0_21]),c_0_14])]),c_0_15]),c_0_456])).

cnf(c_0_465,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,X1,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X2)
    | esk4_3(esk5_0,X1,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,X1,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_458,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_466,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_459,c_0_11])).

cnf(c_0_467,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_460,c_0_455]),c_0_12]),c_0_13]),c_0_11]),c_0_21]),c_0_14])]),c_0_15]),c_0_461])).

cnf(c_0_468,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_462,c_0_455]),c_0_12]),c_0_13]),c_0_11]),c_0_21]),c_0_14])]),c_0_15]),c_0_461])).

cnf(c_0_469,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_463,c_0_406]),c_0_464])).

cnf(c_0_470,plain,
    ( r1_lattice3(X1,X4,X3)
    | r2_hidden(esk3_3(X1,X2,X4),X4)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X2,X4)),X4)
    | ~ r2_yellow_0(X1,esk2_3(X1,X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_471,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_465,c_0_406]),c_0_11])]),c_0_466])).

cnf(c_0_472,plain,
    ( r1_lattice3(X1,X4,X3)
    | r2_hidden(esk3_3(X1,X2,X4),X4)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X2,X4)),X4)
    | esk2_3(X1,X2,X4) != k1_xboole_0
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_473,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,X1)
    | ~ r1_lattice3(esk5_0,esk7_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_467,c_0_406]),c_0_468])).

cnf(c_0_474,plain,
    ( r1_lattice3(X1,X4,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X2,X4) != k1_xboole_0
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X2,X4) != k2_yellow_0(X1,X5)
    | esk2_3(X1,X2,X4) != k1_xboole_0
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_475,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_469,c_0_27]),c_0_28])).

cnf(c_0_476,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_470,c_0_455]),c_0_12]),c_0_13]),c_0_21]),c_0_11]),c_0_14])]),c_0_15]),c_0_471])).

cnf(c_0_477,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_472,c_0_455]),c_0_12]),c_0_13]),c_0_21]),c_0_11]),c_0_14])]),c_0_15]),c_0_471])).

cnf(c_0_478,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_473,c_0_27]),c_0_28])).

cnf(c_0_479,plain,
    ( r1_lattice3(X1,X4,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | esk4_3(X1,X2,X4) != k1_xboole_0
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X2,X4) != k2_yellow_0(X1,X5)
    | ~ r2_yellow_0(X1,esk2_3(X1,X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_480,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | esk3_3(esk5_0,X2,esk7_0) != k2_yellow_0(esk5_0,X3)
    | esk2_3(esk5_0,X2,esk7_0) != k1_xboole_0
    | esk4_3(esk5_0,X2,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_474,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_481,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_475,c_0_34]),c_0_28])).

cnf(c_0_482,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,X1)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_476,c_0_406]),c_0_477])).

cnf(c_0_483,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_478,c_0_34]),c_0_28])).

cnf(c_0_484,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | esk3_3(esk5_0,X2,esk7_0) != k2_yellow_0(esk5_0,X3)
    | esk4_3(esk5_0,X2,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X3)
    | ~ r1_lattice3(esk5_0,X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,X2,esk7_0))
    | ~ r2_yellow_0(esk5_0,X3) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_479,c_0_21]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_485,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_480,c_0_11])).

cnf(c_0_486,plain,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_481,c_0_191]),c_0_192])).

cnf(c_0_487,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_482,c_0_483])).

cnf(c_0_488,plain,
    ( r1_lattice3(X1,X4,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X2,X4)),X4)
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X2,X4) != k2_yellow_0(X1,X5)
    | ~ r2_yellow_0(X1,esk2_3(X1,X2,X4))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_489,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | esk4_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_484,c_0_406]),c_0_11])]),c_0_485])).

cnf(c_0_490,plain,
    ( r1_lattice3(X1,X4,X3)
    | v2_struct_0(X1)
    | ~ r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(k2_yellow_0(X1,esk4_3(X1,X2,X4)),X4)
    | ~ v1_finset_1(X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(X2))
    | ~ r2_yellow_0(X1,X5)
    | esk3_3(X1,X2,X4) != k2_yellow_0(X1,X5)
    | esk2_3(X1,X2,X4) != k1_xboole_0
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_491,plain,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,X1,esk6_0,X2)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_486,c_0_199])).

cnf(c_0_492,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_487,c_0_34]),c_0_28])).

cnf(c_0_493,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,esk2_3(esk5_0,esk6_0,esk7_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_488,c_0_455]),c_0_12]),c_0_13]),c_0_21]),c_0_11]),c_0_14])]),c_0_15]),c_0_489])).

cnf(c_0_494,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | esk2_3(esk5_0,esk6_0,esk7_0) != k1_xboole_0
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_490,c_0_455]),c_0_12]),c_0_13]),c_0_21]),c_0_11]),c_0_14])]),c_0_15]),c_0_489])).

cnf(c_0_495,plain,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | ~ epred1_3(esk6_0,X1,esk5_0)
    | ~ r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_491,c_0_211])]),c_0_212])])).

cnf(c_0_496,negated_conjecture,
    ( r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),esk7_0) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_492]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),c_0_483])).

cnf(c_0_497,plain,
    ( esk8_4(X1,X2,X3,X4) = k1_xboole_0
    | r2_yellow_0(X5,esk8_4(X1,X2,X3,X4))
    | ~ epred1_3(X3,X6,X5)
    | ~ epred1_3(X3,X2,X1)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_191]),c_0_192])).

cnf(c_0_498,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,X1)
    | k2_yellow_0(esk5_0,X2) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X2)
    | ~ r1_lattice3(esk5_0,esk6_0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0))
    | ~ r2_yellow_0(esk5_0,X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_493,c_0_406]),c_0_494])).

cnf(c_0_499,negated_conjecture,
    ( r1_lattice3(esk5_0,esk6_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_495,c_0_496]),c_0_18])])).

cnf(c_0_500,plain,
    ( esk8_4(esk5_0,X1,X2,esk3_3(esk5_0,esk6_0,esk7_0)) = k1_xboole_0
    | r2_yellow_0(X3,esk8_4(esk5_0,X1,X2,esk3_3(esk5_0,esk6_0,esk7_0)))
    | ~ epred1_3(X2,X1,esk5_0)
    | ~ epred1_3(X2,X4,X3)
    | ~ r2_hidden(esk3_3(esk5_0,esk6_0,esk7_0),X1) ),
    inference(spm,[status(thm)],[c_0_497,c_0_212])).

cnf(c_0_501,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(esk1_3(esk5_0,esk6_0,esk7_0),u1_struct_0(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_498,c_0_499])).

cnf(c_0_502,plain,
    ( esk8_4(esk5_0,esk7_0,X1,esk3_3(esk5_0,esk6_0,esk7_0)) = k1_xboole_0
    | r2_yellow_0(X2,esk8_4(esk5_0,esk7_0,X1,esk3_3(esk5_0,esk6_0,esk7_0)))
    | ~ epred1_3(X1,esk7_0,esk5_0)
    | ~ epred1_3(X1,X3,X2) ),
    inference(spm,[status(thm)],[c_0_500,c_0_496])).

cnf(c_0_503,negated_conjecture,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,X1) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk6_0))
    | ~ r2_yellow_0(esk5_0,X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_501,c_0_34]),c_0_28])).

cnf(c_0_504,negated_conjecture,
    ( esk8_4(esk5_0,esk7_0,esk6_0,esk3_3(esk5_0,esk6_0,esk7_0)) = k1_xboole_0
    | r2_yellow_0(X1,esk8_4(esk5_0,esk7_0,esk6_0,esk3_3(esk5_0,esk6_0,esk7_0)))
    | ~ epred1_3(esk6_0,X2,X1) ),
    inference(spm,[status(thm)],[c_0_502,c_0_18])).

cnf(c_0_505,plain,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) != esk3_3(esk5_0,esk6_0,esk7_0)
    | ~ epred1_3(esk6_0,X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_yellow_0(esk5_0,esk8_4(X1,X2,esk6_0,X3)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_503,c_0_191]),c_0_192])).

cnf(c_0_506,negated_conjecture,
    ( esk8_4(esk5_0,esk7_0,esk6_0,esk3_3(esk5_0,esk6_0,esk7_0)) = k1_xboole_0
    | r2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,esk3_3(esk5_0,esk6_0,esk7_0))) ),
    inference(spm,[status(thm)],[c_0_504,c_0_18])).

cnf(c_0_507,negated_conjecture,
    ( esk8_4(esk5_0,esk7_0,esk6_0,esk3_3(esk5_0,esk6_0,esk7_0)) = k1_xboole_0
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | k2_yellow_0(esk5_0,esk8_4(esk5_0,esk7_0,esk6_0,esk3_3(esk5_0,esk6_0,esk7_0))) != esk3_3(esk5_0,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_505,c_0_506]),c_0_18]),c_0_496]),c_0_212])])).

cnf(c_0_508,plain,
    ( esk8_4(esk5_0,esk7_0,esk6_0,esk3_3(esk5_0,esk6_0,esk7_0)) = k1_xboole_0
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_507,c_0_211]),c_0_18]),c_0_496]),c_0_212])])).

cnf(c_0_509,plain,
    ( k2_yellow_0(esk5_0,k1_xboole_0) = esk3_3(esk5_0,esk6_0,esk7_0)
    | r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_211,c_0_508]),c_0_18]),c_0_496]),c_0_212])])).

cnf(c_0_510,plain,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0))
    | r2_yellow_0(esk5_0,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_199,c_0_508]),c_0_18]),c_0_496]),c_0_212])])).

cnf(c_0_511,plain,
    ( k2_yellow_0(esk5_0,k1_xboole_0) = esk3_3(esk5_0,esk6_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_509]),c_0_499]),c_0_23]),c_0_14])]),c_0_28]),c_0_15])).

cnf(c_0_512,plain,
    ( r2_yellow_0(esk5_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_510]),c_0_499]),c_0_23]),c_0_14])]),c_0_28]),c_0_15])).

cnf(c_0_513,plain,
    ( r1_lattice3(esk5_0,esk7_0,esk1_3(esk5_0,esk6_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_505,c_0_508]),c_0_18]),c_0_496]),c_0_212])]),c_0_511]),c_0_512])])).

cnf(c_0_514,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_513]),c_0_499]),c_0_23]),c_0_14])]),c_0_28]),c_0_15]),
    [proof]).

%------------------------------------------------------------------------------
