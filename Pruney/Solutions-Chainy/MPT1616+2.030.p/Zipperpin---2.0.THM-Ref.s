%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KF4kHUAUyM

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:23 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 133 expanded)
%              Number of leaves         :   49 (  66 expanded)
%              Depth                    :   18
%              Number of atoms          :  664 (1038 expanded)
%              Number of equality atoms :   28 (  47 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X48: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X48 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k5_setfam_1 @ X11 @ X10 )
        = ( k3_tarski @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) )
                      & ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )
          & ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
               => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) )
          & ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_10,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_12,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X45: $i] :
      ( ~ ( v2_pre_topc @ X45 )
      | ( r2_hidden @ ( u1_struct_0 @ X45 ) @ ( u1_pre_topc @ X45 ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_setfam_1 @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ ( k3_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_setfam_1 @ ( u1_pre_topc @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X48: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X48 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t60_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( m1_setfam_1 @ B @ A )
      <=> ( ( k5_setfam_1 @ A @ B )
          = A ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_setfam_1 @ X22 @ X21 )
      | ( ( k5_setfam_1 @ X21 @ X22 )
        = X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t60_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( m1_setfam_1 @ ( u1_pre_topc @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X45: $i] :
      ( ~ ( v2_pre_topc @ X45 )
      | ( r2_hidden @ ( u1_struct_0 @ X45 ) @ ( u1_pre_topc @ X45 ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('17',plain,(
    ! [X49: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X49 ) @ X49 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X49 ) )
        = ( k3_tarski @ X49 ) )
      | ( v1_xboole_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('18',plain,(
    ! [X6: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X2 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X6: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X2 ) @ X3 )
      | ~ ( r1_tarski @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X49: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X49 ) )
        = ( k3_tarski @ X49 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X49 ) @ X49 ) ) ),
    inference(clc,[status(thm)],['17','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t24_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
        = ( u1_struct_0 @ A ) ) ) )).

thf(zf_stmt_13,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
          = ( u1_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_yellow_1])).

thf('38',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('39',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('42',plain,(
    ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('46',plain,(
    ( u1_struct_0 @ sk_A )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KF4kHUAUyM
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:04:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.42/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.60  % Solved by: fo/fo7.sh
% 0.42/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.60  % done 209 iterations in 0.111s
% 0.42/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.60  % SZS output start Refutation
% 0.42/0.60  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.42/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.60  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.42/0.60  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.42/0.60  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.42/0.60  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.42/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.42/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.42/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.42/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.60  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.42/0.60  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.42/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.42/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.60  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.42/0.60  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.42/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.60  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.42/0.60  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.42/0.60  thf(dt_u1_pre_topc, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( l1_pre_topc @ A ) =>
% 0.42/0.60       ( m1_subset_1 @
% 0.42/0.60         ( u1_pre_topc @ A ) @ 
% 0.42/0.60         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.42/0.60  thf('0', plain,
% 0.42/0.60      (![X48 : $i]:
% 0.42/0.60         ((m1_subset_1 @ (u1_pre_topc @ X48) @ 
% 0.42/0.60           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48))))
% 0.42/0.60          | ~ (l1_pre_topc @ X48))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.42/0.60  thf(redefinition_k5_setfam_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.60       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.42/0.60  thf('1', plain,
% 0.42/0.60      (![X10 : $i, X11 : $i]:
% 0.42/0.60         (((k5_setfam_1 @ X11 @ X10) = (k3_tarski @ X10))
% 0.42/0.60          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.42/0.60      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.42/0.60  thf('2', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (l1_pre_topc @ X0)
% 0.42/0.60          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.42/0.60              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.60  thf(d1_pre_topc, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( l1_pre_topc @ A ) =>
% 0.42/0.60       ( ( v2_pre_topc @ A ) <=>
% 0.42/0.60         ( ( ![B:$i]:
% 0.42/0.60             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.60               ( ![C:$i]:
% 0.42/0.60                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.60                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.42/0.60                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.42/0.60                     ( r2_hidden @
% 0.42/0.60                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.42/0.60                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.42/0.60           ( ![B:$i]:
% 0.42/0.60             ( ( m1_subset_1 @
% 0.42/0.60                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.60               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.42/0.60                 ( r2_hidden @
% 0.42/0.60                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.42/0.60                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.42/0.60           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $o).
% 0.42/0.60  thf(zf_stmt_1, axiom,
% 0.42/0.60    (![B:$i,A:$i]:
% 0.42/0.60     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.42/0.60       ( ( m1_subset_1 @
% 0.42/0.60           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.60         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.42/0.60  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 0.42/0.60  thf(zf_stmt_3, axiom,
% 0.42/0.60    (![B:$i,A:$i]:
% 0.42/0.60     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.42/0.60       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.42/0.60         ( r2_hidden @
% 0.42/0.60           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $o).
% 0.42/0.60  thf(zf_stmt_5, axiom,
% 0.42/0.60    (![B:$i,A:$i]:
% 0.42/0.60     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.42/0.60       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.60         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_6, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.42/0.60  thf(zf_stmt_7, axiom,
% 0.42/0.60    (![C:$i,B:$i,A:$i]:
% 0.42/0.60     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.42/0.60       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.60         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.42/0.60  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.42/0.60  thf(zf_stmt_9, axiom,
% 0.42/0.60    (![C:$i,B:$i,A:$i]:
% 0.42/0.60     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.42/0.60       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.42/0.60         ( r2_hidden @
% 0.42/0.60           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_10, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.42/0.60  thf(zf_stmt_11, axiom,
% 0.42/0.60    (![C:$i,B:$i,A:$i]:
% 0.42/0.60     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.42/0.60       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.42/0.60         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.42/0.60  thf(zf_stmt_12, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( l1_pre_topc @ A ) =>
% 0.42/0.60       ( ( v2_pre_topc @ A ) <=>
% 0.42/0.60         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.42/0.60           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.42/0.60           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.42/0.60  thf('3', plain,
% 0.42/0.60      (![X45 : $i]:
% 0.42/0.60         (~ (v2_pre_topc @ X45)
% 0.42/0.60          | (r2_hidden @ (u1_struct_0 @ X45) @ (u1_pre_topc @ X45))
% 0.42/0.60          | ~ (l1_pre_topc @ X45))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.42/0.60  thf(l49_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.42/0.60  thf('4', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((r1_tarski @ X0 @ (k3_tarski @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.42/0.60  thf('5', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (l1_pre_topc @ X0)
% 0.42/0.60          | ~ (v2_pre_topc @ X0)
% 0.42/0.60          | (r1_tarski @ (u1_struct_0 @ X0) @ (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.42/0.60  thf(d12_setfam_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.42/0.60  thf('6', plain,
% 0.42/0.60      (![X7 : $i, X9 : $i]:
% 0.42/0.60         ((m1_setfam_1 @ X9 @ X7) | ~ (r1_tarski @ X7 @ (k3_tarski @ X9)))),
% 0.42/0.60      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.42/0.60  thf('7', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v2_pre_topc @ X0)
% 0.42/0.60          | ~ (l1_pre_topc @ X0)
% 0.42/0.60          | (m1_setfam_1 @ (u1_pre_topc @ X0) @ (u1_struct_0 @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.60  thf('8', plain,
% 0.42/0.60      (![X48 : $i]:
% 0.42/0.60         ((m1_subset_1 @ (u1_pre_topc @ X48) @ 
% 0.42/0.60           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48))))
% 0.42/0.60          | ~ (l1_pre_topc @ X48))),
% 0.42/0.60      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.42/0.60  thf(t60_setfam_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.60       ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ))).
% 0.42/0.60  thf('9', plain,
% 0.42/0.60      (![X21 : $i, X22 : $i]:
% 0.42/0.60         (~ (m1_setfam_1 @ X22 @ X21)
% 0.42/0.60          | ((k5_setfam_1 @ X21 @ X22) = (X21))
% 0.42/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 0.42/0.60      inference('cnf', [status(esa)], [t60_setfam_1])).
% 0.42/0.60  thf('10', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (l1_pre_topc @ X0)
% 0.42/0.60          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.42/0.60              = (u1_struct_0 @ X0))
% 0.42/0.60          | ~ (m1_setfam_1 @ (u1_pre_topc @ X0) @ (u1_struct_0 @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.60  thf('11', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (l1_pre_topc @ X0)
% 0.42/0.60          | ~ (v2_pre_topc @ X0)
% 0.42/0.60          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.42/0.60              = (u1_struct_0 @ X0))
% 0.42/0.60          | ~ (l1_pre_topc @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['7', '10'])).
% 0.42/0.60  thf('12', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.42/0.60            = (u1_struct_0 @ X0))
% 0.42/0.60          | ~ (v2_pre_topc @ X0)
% 0.42/0.60          | ~ (l1_pre_topc @ X0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['11'])).
% 0.42/0.60  thf('13', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0))
% 0.42/0.60          | ~ (l1_pre_topc @ X0)
% 0.42/0.60          | ~ (l1_pre_topc @ X0)
% 0.42/0.60          | ~ (v2_pre_topc @ X0))),
% 0.42/0.60      inference('sup+', [status(thm)], ['2', '12'])).
% 0.42/0.60  thf('14', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v2_pre_topc @ X0)
% 0.42/0.60          | ~ (l1_pre_topc @ X0)
% 0.42/0.60          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['13'])).
% 0.42/0.60  thf('15', plain,
% 0.42/0.60      (![X45 : $i]:
% 0.42/0.60         (~ (v2_pre_topc @ X45)
% 0.42/0.60          | (r2_hidden @ (u1_struct_0 @ X45) @ (u1_pre_topc @ X45))
% 0.42/0.60          | ~ (l1_pre_topc @ X45))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.42/0.60  thf('16', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (v2_pre_topc @ X0)
% 0.42/0.60          | ~ (l1_pre_topc @ X0)
% 0.42/0.60          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0)))),
% 0.42/0.60      inference('simplify', [status(thm)], ['13'])).
% 0.42/0.60  thf(t14_yellow_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.60       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.42/0.60         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.42/0.60  thf('17', plain,
% 0.42/0.60      (![X49 : $i]:
% 0.42/0.60         (~ (r2_hidden @ (k3_tarski @ X49) @ X49)
% 0.42/0.60          | ((k4_yellow_0 @ (k2_yellow_1 @ X49)) = (k3_tarski @ X49))
% 0.42/0.60          | (v1_xboole_0 @ X49))),
% 0.42/0.60      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.42/0.60  thf(t99_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.42/0.60  thf('18', plain, (![X6 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X6)) = (X6))),
% 0.42/0.60      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.42/0.60  thf(t94_zfmisc_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.42/0.60       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.42/0.60  thf('19', plain,
% 0.42/0.60      (![X2 : $i, X3 : $i]:
% 0.42/0.60         ((r1_tarski @ (k3_tarski @ X2) @ X3)
% 0.42/0.60          | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 0.42/0.60      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.42/0.60  thf('20', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((r1_tarski @ X0 @ (k3_tarski @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.42/0.60  thf('21', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.42/0.60          | (r1_tarski @ (sk_C @ X1 @ X0) @ (k3_tarski @ X0)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.42/0.60  thf('22', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((r1_tarski @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X0)
% 0.42/0.60          | (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X1))),
% 0.42/0.60      inference('sup+', [status(thm)], ['18', '21'])).
% 0.42/0.60  thf('23', plain, (![X6 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X6)) = (X6))),
% 0.42/0.60      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         ((r1_tarski @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X0)
% 0.42/0.60          | (r1_tarski @ X0 @ X1))),
% 0.42/0.60      inference('demod', [status(thm)], ['22', '23'])).
% 0.42/0.60  thf('25', plain,
% 0.42/0.60      (![X2 : $i, X3 : $i]:
% 0.42/0.60         ((r1_tarski @ (k3_tarski @ X2) @ X3)
% 0.42/0.60          | ~ (r1_tarski @ (sk_C @ X3 @ X2) @ X3))),
% 0.42/0.60      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.42/0.60  thf('26', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         ((r1_tarski @ X0 @ X0)
% 0.42/0.60          | (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.42/0.60  thf('27', plain, (![X6 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X6)) = (X6))),
% 0.42/0.60      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.42/0.60  thf('28', plain,
% 0.42/0.60      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.42/0.60      inference('demod', [status(thm)], ['26', '27'])).
% 0.42/0.60  thf('29', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.42/0.60      inference('simplify', [status(thm)], ['28'])).
% 0.42/0.60  thf(t3_subset, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.60  thf('30', plain,
% 0.42/0.60      (![X12 : $i, X14 : $i]:
% 0.42/0.60         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.42/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.60  thf('31', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.42/0.60  thf(t5_subset, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.42/0.60          ( v1_xboole_0 @ C ) ) ))).
% 0.42/0.60  thf('32', plain,
% 0.42/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.60         (~ (r2_hidden @ X18 @ X19)
% 0.42/0.60          | ~ (v1_xboole_0 @ X20)
% 0.42/0.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.42/0.60      inference('cnf', [status(esa)], [t5_subset])).
% 0.42/0.60  thf('33', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.42/0.60  thf('34', plain,
% 0.42/0.60      (![X49 : $i]:
% 0.42/0.60         (((k4_yellow_0 @ (k2_yellow_1 @ X49)) = (k3_tarski @ X49))
% 0.42/0.60          | ~ (r2_hidden @ (k3_tarski @ X49) @ X49))),
% 0.42/0.60      inference('clc', [status(thm)], ['17', '33'])).
% 0.42/0.60  thf('35', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.42/0.60          | ~ (l1_pre_topc @ X0)
% 0.42/0.60          | ~ (v2_pre_topc @ X0)
% 0.42/0.60          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.42/0.60              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.42/0.60      inference('sup-', [status(thm)], ['16', '34'])).
% 0.42/0.60  thf('36', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (~ (l1_pre_topc @ X0)
% 0.42/0.60          | ~ (v2_pre_topc @ X0)
% 0.42/0.60          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.42/0.60              = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.42/0.60          | ~ (v2_pre_topc @ X0)
% 0.42/0.60          | ~ (l1_pre_topc @ X0))),
% 0.42/0.60      inference('sup-', [status(thm)], ['15', '35'])).
% 0.42/0.60  thf('37', plain,
% 0.42/0.60      (![X0 : $i]:
% 0.42/0.60         (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.42/0.60            = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.42/0.60          | ~ (v2_pre_topc @ X0)
% 0.42/0.60          | ~ (l1_pre_topc @ X0))),
% 0.42/0.60      inference('simplify', [status(thm)], ['36'])).
% 0.42/0.60  thf(t24_yellow_1, conjecture,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.60       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.42/0.60         ( u1_struct_0 @ A ) ) ))).
% 0.42/0.60  thf(zf_stmt_13, negated_conjecture,
% 0.42/0.60    (~( ![A:$i]:
% 0.42/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.42/0.60            ( l1_pre_topc @ A ) ) =>
% 0.42/0.60          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.42/0.60            ( u1_struct_0 @ A ) ) ) )),
% 0.42/0.60    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 0.42/0.60  thf('38', plain,
% 0.42/0.60      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.42/0.60         != (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.42/0.60  thf('39', plain,
% 0.42/0.60      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 0.42/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.42/0.60        | ~ (v2_pre_topc @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.42/0.60  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.42/0.60  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.42/0.60  thf('42', plain,
% 0.42/0.60      (((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.42/0.60  thf('43', plain,
% 0.42/0.60      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.42/0.60        | ~ (l1_pre_topc @ sk_A)
% 0.42/0.60        | ~ (v2_pre_topc @ sk_A))),
% 0.42/0.60      inference('sup-', [status(thm)], ['14', '42'])).
% 0.42/0.60  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.42/0.60  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.42/0.60  thf('46', plain, (((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))),
% 0.42/0.60      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.42/0.60  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.45/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
