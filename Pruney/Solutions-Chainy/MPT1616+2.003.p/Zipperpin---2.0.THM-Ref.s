%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vfeic243vb

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 125 expanded)
%              Number of leaves         :   47 (  62 expanded)
%              Depth                    :   17
%              Number of atoms          :  596 ( 989 expanded)
%              Number of equality atoms :   26 (  47 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X46: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X46 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k5_setfam_1 @ X9 @ X8 )
        = ( k3_tarski @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
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
    ! [X43: $i] :
      ( ~ ( v2_pre_topc @ X43 )
      | ( r2_hidden @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X15 @ X13 )
      | ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_setfam_1 @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ ( k3_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_setfam_1 @ ( u1_pre_topc @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X46: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X46 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t60_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( m1_setfam_1 @ B @ A )
      <=> ( ( k5_setfam_1 @ A @ B )
          = A ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_setfam_1 @ X20 @ X19 )
      | ( ( k5_setfam_1 @ X19 @ X20 )
        = X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t60_setfam_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( m1_setfam_1 @ ( u1_pre_topc @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X43: $i] :
      ( ~ ( v2_pre_topc @ X43 )
      | ( r2_hidden @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('20',plain,(
    ! [X47: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X47 ) @ X47 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X47 ) )
        = ( k3_tarski @ X47 ) )
      | ( v1_xboole_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf('21',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X47: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X47 ) )
        = ( k3_tarski @ X47 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X47 ) @ X47 ) ) ),
    inference(clc,[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

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

thf('30',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('31',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('34',plain,(
    ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('37',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('38',plain,(
    ( u1_struct_0 @ sk_A )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    $false ),
    inference(simplify,[status(thm)],['38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vfeic243vb
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:35:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 152 iterations in 0.072s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.53  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.53  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.21/0.53  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.21/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.21/0.53  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.53  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.53  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.53  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.21/0.53  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.21/0.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.53  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.53  thf(dt_u1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( m1_subset_1 @
% 0.21/0.53         ( u1_pre_topc @ A ) @ 
% 0.21/0.53         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X46 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (u1_pre_topc @ X46) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46))))
% 0.21/0.53          | ~ (l1_pre_topc @ X46))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.53  thf(redefinition_k5_setfam_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.53       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         (((k5_setfam_1 @ X9 @ X8) = (k3_tarski @ X8))
% 0.21/0.53          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.53              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf(d1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ( v2_pre_topc @ A ) <=>
% 0.21/0.53         ( ( ![B:$i]:
% 0.21/0.53             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53               ( ![C:$i]:
% 0.21/0.53                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.53                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.21/0.53                     ( r2_hidden @
% 0.21/0.53                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.21/0.53                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.21/0.53           ( ![B:$i]:
% 0.21/0.53             ( ( m1_subset_1 @
% 0.21/0.53                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.53               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.21/0.53                 ( r2_hidden @
% 0.21/0.53                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.21/0.53                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.21/0.53           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_1, axiom,
% 0.21/0.53    (![B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.21/0.53       ( ( m1_subset_1 @
% 0.21/0.53           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.53         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.21/0.53  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_3, axiom,
% 0.21/0.53    (![B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.21/0.53       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.21/0.53         ( r2_hidden @
% 0.21/0.53           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_5, axiom,
% 0.21/0.53    (![B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.21/0.53       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_6, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_7, axiom,
% 0.21/0.53    (![C:$i,B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.21/0.53       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.53         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.21/0.53  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_9, axiom,
% 0.21/0.53    (![C:$i,B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.21/0.53       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.21/0.53         ( r2_hidden @
% 0.21/0.53           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_10, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_11, axiom,
% 0.21/0.53    (![C:$i,B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.21/0.53       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.53         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_12, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ( v2_pre_topc @ A ) <=>
% 0.21/0.53         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.53           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.21/0.53           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X43 : $i]:
% 0.21/0.53         (~ (v2_pre_topc @ X43)
% 0.21/0.53          | (r2_hidden @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))
% 0.21/0.53          | ~ (l1_pre_topc @ X43))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.53  thf(t56_setfam_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.21/0.53       ( r1_tarski @ C @ B ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.53         (~ (r1_tarski @ (k3_tarski @ X13) @ X14)
% 0.21/0.53          | ~ (r2_hidden @ X15 @ X13)
% 0.21/0.53          | (r1_tarski @ X15 @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ (k3_tarski @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | (r1_tarski @ (u1_struct_0 @ X0) @ (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '7'])).
% 0.21/0.53  thf(d12_setfam_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X5 : $i, X7 : $i]:
% 0.21/0.53         ((m1_setfam_1 @ X7 @ X5) | ~ (r1_tarski @ X5 @ (k3_tarski @ X7)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | (m1_setfam_1 @ (u1_pre_topc @ X0) @ (u1_struct_0 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X46 : $i]:
% 0.21/0.53         ((m1_subset_1 @ (u1_pre_topc @ X46) @ 
% 0.21/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46))))
% 0.21/0.53          | ~ (l1_pre_topc @ X46))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.53  thf(t60_setfam_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.53       ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X19 : $i, X20 : $i]:
% 0.21/0.53         (~ (m1_setfam_1 @ X20 @ X19)
% 0.21/0.53          | ((k5_setfam_1 @ X19 @ X20) = (X19))
% 0.21/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.21/0.53      inference('cnf', [status(esa)], [t60_setfam_1])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.53              = (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (m1_setfam_1 @ (u1_pre_topc @ X0) @ (u1_struct_0 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.53              = (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.53            = (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0))
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['2', '15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X43 : $i]:
% 0.21/0.53         (~ (v2_pre_topc @ X43)
% 0.21/0.53          | (r2_hidden @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43))
% 0.21/0.53          | ~ (l1_pre_topc @ X43))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['16'])).
% 0.21/0.53  thf(t14_yellow_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.53       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.21/0.53         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X47 : $i]:
% 0.21/0.53         (~ (r2_hidden @ (k3_tarski @ X47) @ X47)
% 0.21/0.53          | ((k4_yellow_0 @ (k2_yellow_1 @ X47)) = (k3_tarski @ X47))
% 0.21/0.53          | (v1_xboole_0 @ X47))),
% 0.21/0.53      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.21/0.53  thf('21', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.53      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.53  thf(t3_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X10 : $i, X12 : $i]:
% 0.21/0.53         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.53  thf('23', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf(t5_subset, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.53          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X16 @ X17)
% 0.21/0.53          | ~ (v1_xboole_0 @ X18)
% 0.21/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X47 : $i]:
% 0.21/0.53         (((k4_yellow_0 @ (k2_yellow_1 @ X47)) = (k3_tarski @ X47))
% 0.21/0.53          | ~ (r2_hidden @ (k3_tarski @ X47) @ X47))),
% 0.21/0.53      inference('clc', [status(thm)], ['20', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.53          | ~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.21/0.53              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['19', '26'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X0)
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.21/0.53              = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.21/0.53            = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.21/0.53          | ~ (v2_pre_topc @ X0)
% 0.21/0.53          | ~ (l1_pre_topc @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.53  thf(t24_yellow_1, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.53       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.21/0.53         ( u1_struct_0 @ A ) ) ))).
% 0.21/0.53  thf(zf_stmt_13, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.53            ( l1_pre_topc @ A ) ) =>
% 0.21/0.53          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.21/0.53            ( u1_struct_0 @ A ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.21/0.53         != (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 0.21/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53        | ~ (v2_pre_topc @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.21/0.53  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.21/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.53        | ~ (v2_pre_topc @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '34'])).
% 0.21/0.53  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.21/0.53  thf('37', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.21/0.53  thf('38', plain, (((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.21/0.53  thf('39', plain, ($false), inference('simplify', [status(thm)], ['38'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
