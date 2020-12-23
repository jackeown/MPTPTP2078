%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bi5P0zUKIr

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:21 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 234 expanded)
%              Number of leaves         :   46 (  94 expanded)
%              Depth                    :   17
%              Number of atoms          :  636 (1891 expanded)
%              Number of equality atoms :   18 (  66 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X42: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X42 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( r2_hidden @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X14: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ ( k3_tarski @ X10 ) )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('7',plain,(
    ! [X13: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X11 ) @ ( k3_tarski @ X12 ) )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X13: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t24_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
        = ( u1_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
          = ( u1_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_yellow_1])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_12,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_13,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X39: $i,X41: $i] :
      ( ~ ( v2_pre_topc @ X39 )
      | ( zip_tseitin_5 @ X41 @ X39 )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( zip_tseitin_5 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X42: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X42 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('19',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) )
      | ( zip_tseitin_4 @ X36 @ X37 )
      | ~ ( zip_tseitin_5 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( zip_tseitin_5 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( zip_tseitin_4 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    zip_tseitin_4 @ ( u1_pre_topc @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['21','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ X33 @ ( u1_pre_topc @ X34 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X34 ) @ X33 ) @ ( u1_pre_topc @ X34 ) )
      | ~ ( zip_tseitin_4 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    ! [X39: $i] :
      ( ~ ( v2_pre_topc @ X39 )
      | ( r2_hidden @ ( u1_struct_0 @ X39 ) @ ( u1_pre_topc @ X39 ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('30',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X17 @ X20 )
      | ~ ( r2_hidden @ X19 @ ( u1_pre_topc @ X20 ) )
      | ~ ( r2_hidden @ X17 @ ( u1_pre_topc @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X19 @ ( u1_pre_topc @ X18 ) )
      | ~ ( zip_tseitin_0 @ X19 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('37',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ ( k3_tarski @ X10 ) )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('39',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,
    ( ~ ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('45',plain,(
    ! [X43: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X43 ) @ X43 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X43 ) )
        = ( k3_tarski @ X43 ) )
      | ( v1_xboole_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('47',plain,(
    ! [X43: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X43 ) )
        = ( k3_tarski @ X43 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X43 ) @ X43 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
      = ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('50',plain,
    ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('51',plain,
    ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Bi5P0zUKIr
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:08:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 190 iterations in 0.148s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.46/0.63  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.46/0.63  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.46/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.63  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.46/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.63  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.46/0.63  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.46/0.63  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.46/0.63  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.46/0.63  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.46/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.46/0.63  thf(dt_u1_pre_topc, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( m1_subset_1 @
% 0.46/0.63         ( u1_pre_topc @ A ) @ 
% 0.46/0.63         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.46/0.63  thf('0', plain,
% 0.46/0.63      (![X42 : $i]:
% 0.46/0.63         ((m1_subset_1 @ (u1_pre_topc @ X42) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42))))
% 0.46/0.63          | ~ (l1_pre_topc @ X42))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.46/0.63  thf(t2_subset, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ A @ B ) =>
% 0.46/0.63       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      (![X15 : $i, X16 : $i]:
% 0.46/0.63         ((r2_hidden @ X15 @ X16)
% 0.46/0.63          | (v1_xboole_0 @ X16)
% 0.46/0.63          | ~ (m1_subset_1 @ X15 @ X16))),
% 0.46/0.63      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X0)
% 0.46/0.63          | (v1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.46/0.63          | (r2_hidden @ (u1_pre_topc @ X0) @ 
% 0.46/0.63             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.63  thf(fc1_subset_1, axiom,
% 0.46/0.63    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.63  thf('3', plain, (![X14 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((r2_hidden @ (u1_pre_topc @ X0) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.46/0.63          | ~ (l1_pre_topc @ X0))),
% 0.46/0.63      inference('clc', [status(thm)], ['2', '3'])).
% 0.46/0.63  thf(l49_zfmisc_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.46/0.63  thf('5', plain,
% 0.46/0.63      (![X9 : $i, X10 : $i]:
% 0.46/0.63         ((r1_tarski @ X9 @ (k3_tarski @ X10)) | ~ (r2_hidden @ X9 @ X10))),
% 0.46/0.63      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X0)
% 0.46/0.63          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 0.46/0.63             (k3_tarski @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.63  thf(t99_zfmisc_1, axiom,
% 0.46/0.63    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.46/0.63  thf('7', plain, (![X13 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X13)) = (X13))),
% 0.46/0.63      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.46/0.63  thf('8', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X0)
% 0.46/0.63          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 0.46/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.46/0.63      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.63  thf(t95_zfmisc_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( r1_tarski @ A @ B ) =>
% 0.46/0.63       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (![X11 : $i, X12 : $i]:
% 0.46/0.63         ((r1_tarski @ (k3_tarski @ X11) @ (k3_tarski @ X12))
% 0.46/0.63          | ~ (r1_tarski @ X11 @ X12))),
% 0.46/0.63      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X0)
% 0.46/0.63          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 0.46/0.63             (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.63  thf('11', plain, (![X13 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X13)) = (X13))),
% 0.46/0.63      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X0)
% 0.46/0.63          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.63  thf(t24_yellow_1, conjecture,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.63       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.46/0.63         ( u1_struct_0 @ A ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i]:
% 0.46/0.63        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.63            ( l1_pre_topc @ A ) ) =>
% 0.46/0.63          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.46/0.63            ( u1_struct_0 @ A ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 0.46/0.63  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(d1_pre_topc, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ( v2_pre_topc @ A ) <=>
% 0.46/0.63         ( ( ![B:$i]:
% 0.46/0.63             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63               ( ![C:$i]:
% 0.46/0.63                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.46/0.63                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.46/0.63                     ( r2_hidden @
% 0.46/0.63                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.46/0.63                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.46/0.63           ( ![B:$i]:
% 0.46/0.63             ( ( m1_subset_1 @
% 0.46/0.63                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.63               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.46/0.63                 ( r2_hidden @
% 0.46/0.63                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.46/0.63                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.46/0.63           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 0.46/0.63  thf(zf_stmt_2, axiom,
% 0.46/0.63    (![B:$i,A:$i]:
% 0.46/0.63     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.46/0.63       ( ( m1_subset_1 @
% 0.46/0.63           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.63         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.46/0.63  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.46/0.63  thf(zf_stmt_4, axiom,
% 0.46/0.63    (![B:$i,A:$i]:
% 0.46/0.63     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.46/0.63       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.46/0.63         ( r2_hidden @
% 0.46/0.63           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.46/0.63  thf(zf_stmt_6, axiom,
% 0.46/0.63    (![B:$i,A:$i]:
% 0.46/0.63     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.46/0.63       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.46/0.63  thf(zf_stmt_8, axiom,
% 0.46/0.63    (![C:$i,B:$i,A:$i]:
% 0.46/0.63     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.46/0.63       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.63         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.46/0.63  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.63  thf(zf_stmt_10, axiom,
% 0.46/0.63    (![C:$i,B:$i,A:$i]:
% 0.46/0.63     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.46/0.63       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.46/0.63         ( r2_hidden @
% 0.46/0.63           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.46/0.63  thf(zf_stmt_12, axiom,
% 0.46/0.63    (![C:$i,B:$i,A:$i]:
% 0.46/0.63     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.46/0.63       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.46/0.63         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_13, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_pre_topc @ A ) =>
% 0.46/0.63       ( ( v2_pre_topc @ A ) <=>
% 0.46/0.63         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.46/0.63           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.46/0.63           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      (![X39 : $i, X41 : $i]:
% 0.46/0.63         (~ (v2_pre_topc @ X39)
% 0.46/0.63          | (zip_tseitin_5 @ X41 @ X39)
% 0.46/0.63          | ~ (l1_pre_topc @ X39))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      (![X0 : $i]: ((zip_tseitin_5 @ X0 @ sk_A) | ~ (v2_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.63  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('17', plain, (![X0 : $i]: (zip_tseitin_5 @ X0 @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      (![X42 : $i]:
% 0.46/0.63         ((m1_subset_1 @ (u1_pre_topc @ X42) @ 
% 0.46/0.63           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42))))
% 0.46/0.63          | ~ (l1_pre_topc @ X42))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (![X36 : $i, X37 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X36 @ 
% 0.46/0.63             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37))))
% 0.46/0.63          | (zip_tseitin_4 @ X36 @ X37)
% 0.46/0.63          | ~ (zip_tseitin_5 @ X36 @ X37))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X0)
% 0.46/0.63          | ~ (zip_tseitin_5 @ (u1_pre_topc @ X0) @ X0)
% 0.46/0.63          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      (((zip_tseitin_4 @ (u1_pre_topc @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['17', '20'])).
% 0.46/0.63  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('23', plain, ((zip_tseitin_4 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.63  thf(d10_xboole_0, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.46/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.63  thf('25', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.46/0.63      inference('simplify', [status(thm)], ['24'])).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      (![X33 : $i, X34 : $i]:
% 0.46/0.63         (~ (r1_tarski @ X33 @ (u1_pre_topc @ X34))
% 0.46/0.63          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X34) @ X33) @ 
% 0.46/0.63             (u1_pre_topc @ X34))
% 0.46/0.63          | ~ (zip_tseitin_4 @ X33 @ X34))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 0.46/0.63          | (r2_hidden @ 
% 0.46/0.63             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 0.46/0.63             (u1_pre_topc @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.63  thf('28', plain,
% 0.46/0.63      ((r2_hidden @ 
% 0.46/0.63        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.46/0.63        (u1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['23', '27'])).
% 0.46/0.63  thf('29', plain,
% 0.46/0.63      (![X39 : $i]:
% 0.46/0.63         (~ (v2_pre_topc @ X39)
% 0.46/0.63          | (r2_hidden @ (u1_struct_0 @ X39) @ (u1_pre_topc @ X39))
% 0.46/0.63          | ~ (l1_pre_topc @ X39))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.46/0.63  thf('30', plain,
% 0.46/0.63      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.46/0.63         ((zip_tseitin_0 @ X19 @ X17 @ X20)
% 0.46/0.63          | ~ (r2_hidden @ X19 @ (u1_pre_topc @ X20))
% 0.46/0.63          | ~ (r2_hidden @ X17 @ (u1_pre_topc @ X20)))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (l1_pre_topc @ X0)
% 0.46/0.63          | ~ (v2_pre_topc @ X0)
% 0.46/0.63          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0))
% 0.46/0.63          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ X0))),
% 0.46/0.63      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.63  thf('32', plain,
% 0.46/0.63      (((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63         (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_A)
% 0.46/0.63        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['28', '31'])).
% 0.46/0.63  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('35', plain,
% 0.46/0.63      ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_A)),
% 0.46/0.63      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.46/0.63  thf('36', plain,
% 0.46/0.63      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.63         ((r2_hidden @ X19 @ (u1_pre_topc @ X18))
% 0.46/0.63          | ~ (zip_tseitin_0 @ X19 @ X17 @ X18))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.46/0.63  thf('37', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.63  thf('38', plain,
% 0.46/0.63      (![X9 : $i, X10 : $i]:
% 0.46/0.63         ((r1_tarski @ X9 @ (k3_tarski @ X10)) | ~ (r2_hidden @ X9 @ X10))),
% 0.46/0.63      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.46/0.63  thf('39', plain,
% 0.46/0.63      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ (u1_pre_topc @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf('40', plain,
% 0.46/0.63      (![X3 : $i, X5 : $i]:
% 0.46/0.63         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.46/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.63  thf('41', plain,
% 0.46/0.63      ((~ (r1_tarski @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ 
% 0.46/0.63           (u1_struct_0 @ sk_A))
% 0.46/0.63        | ((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.63  thf('42', plain,
% 0.46/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.63        | ((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['12', '41'])).
% 0.46/0.63  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('44', plain,
% 0.46/0.63      (((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['42', '43'])).
% 0.46/0.63  thf(t14_yellow_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.63       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.46/0.63         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.46/0.63  thf('45', plain,
% 0.46/0.63      (![X43 : $i]:
% 0.46/0.63         (~ (r2_hidden @ (k3_tarski @ X43) @ X43)
% 0.46/0.63          | ((k4_yellow_0 @ (k2_yellow_1 @ X43)) = (k3_tarski @ X43))
% 0.46/0.63          | (v1_xboole_0 @ X43))),
% 0.46/0.63      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.46/0.63  thf(d1_xboole_0, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.63  thf('46', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.63  thf('47', plain,
% 0.46/0.63      (![X43 : $i]:
% 0.46/0.63         (((k4_yellow_0 @ (k2_yellow_1 @ X43)) = (k3_tarski @ X43))
% 0.46/0.63          | ~ (r2_hidden @ (k3_tarski @ X43) @ X43))),
% 0.46/0.63      inference('clc', [status(thm)], ['45', '46'])).
% 0.46/0.63  thf('48', plain,
% 0.46/0.63      ((~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.46/0.63        | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.46/0.63            = (k3_tarski @ (u1_pre_topc @ sk_A))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['44', '47'])).
% 0.46/0.63  thf('49', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.63  thf('50', plain,
% 0.46/0.63      (((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['42', '43'])).
% 0.46/0.63  thf('51', plain,
% 0.46/0.63      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.46/0.63         = (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.46/0.63  thf('52', plain,
% 0.46/0.63      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.46/0.63         != (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('53', plain, ($false),
% 0.46/0.63      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
