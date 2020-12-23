%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EzHBdbizhz

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:02 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 110 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  631 (1502 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t50_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X18 @ X17 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r1_tarski @ X27 @ X29 )
      | ( r1_tarski @ ( k1_tops_1 @ X28 @ X27 ) @ ( k1_tops_1 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('27',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X26 @ X25 ) @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X26 @ X25 ) @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ( r1_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ X16 )
      | ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['12','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EzHBdbizhz
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:10:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 1.07/1.27  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.07/1.27  % Solved by: fo/fo7.sh
% 1.07/1.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.27  % done 1409 iterations in 0.806s
% 1.07/1.27  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.07/1.27  % SZS output start Refutation
% 1.07/1.27  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.07/1.27  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.07/1.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.27  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.07/1.27  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.27  thf(sk_C_type, type, sk_C: $i).
% 1.07/1.27  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.07/1.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.27  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.27  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.07/1.27  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.07/1.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.27  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.07/1.27  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.07/1.27  thf(t50_tops_1, conjecture,
% 1.07/1.27    (![A:$i]:
% 1.07/1.27     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.07/1.27       ( ![B:$i]:
% 1.07/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.27           ( ![C:$i]:
% 1.07/1.27             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.27               ( r1_tarski @
% 1.07/1.27                 ( k1_tops_1 @
% 1.07/1.27                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 1.07/1.27                 ( k7_subset_1 @
% 1.07/1.27                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 1.07/1.27                   ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.07/1.27  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.27    (~( ![A:$i]:
% 1.07/1.27        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.07/1.27          ( ![B:$i]:
% 1.07/1.27            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.27              ( ![C:$i]:
% 1.07/1.27                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.27                  ( r1_tarski @
% 1.07/1.27                    ( k1_tops_1 @
% 1.07/1.27                      A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 1.07/1.27                    ( k7_subset_1 @
% 1.07/1.27                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 1.07/1.27                      ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 1.07/1.27    inference('cnf.neg', [status(esa)], [t50_tops_1])).
% 1.07/1.27  thf('0', plain,
% 1.07/1.27      (~ (r1_tarski @ 
% 1.07/1.27          (k1_tops_1 @ sk_A @ 
% 1.07/1.27           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 1.07/1.27          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.07/1.27           (k1_tops_1 @ sk_A @ sk_C)))),
% 1.07/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.27  thf('1', plain,
% 1.07/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.27  thf(redefinition_k7_subset_1, axiom,
% 1.07/1.27    (![A:$i,B:$i,C:$i]:
% 1.07/1.27     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.07/1.27       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.07/1.27  thf('2', plain,
% 1.07/1.27      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.07/1.27         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 1.07/1.27          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 1.07/1.27      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.07/1.27  thf('3', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.07/1.27           = (k4_xboole_0 @ sk_B @ X0))),
% 1.07/1.27      inference('sup-', [status(thm)], ['1', '2'])).
% 1.07/1.27  thf('4', plain,
% 1.07/1.27      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 1.07/1.27          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.07/1.27           (k1_tops_1 @ sk_A @ sk_C)))),
% 1.07/1.27      inference('demod', [status(thm)], ['0', '3'])).
% 1.07/1.27  thf('5', plain,
% 1.07/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.27  thf(dt_k1_tops_1, axiom,
% 1.07/1.27    (![A:$i,B:$i]:
% 1.07/1.27     ( ( ( l1_pre_topc @ A ) & 
% 1.07/1.27         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.07/1.27       ( m1_subset_1 @
% 1.07/1.27         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.07/1.27  thf('6', plain,
% 1.07/1.27      (![X23 : $i, X24 : $i]:
% 1.07/1.27         (~ (l1_pre_topc @ X23)
% 1.07/1.27          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.07/1.27          | (m1_subset_1 @ (k1_tops_1 @ X23 @ X24) @ 
% 1.07/1.27             (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 1.07/1.27      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.07/1.27  thf('7', plain,
% 1.07/1.27      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.07/1.27         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.07/1.27        | ~ (l1_pre_topc @ sk_A))),
% 1.07/1.27      inference('sup-', [status(thm)], ['5', '6'])).
% 1.07/1.27  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.27  thf('9', plain,
% 1.07/1.27      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.07/1.27        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.27      inference('demod', [status(thm)], ['7', '8'])).
% 1.07/1.27  thf('10', plain,
% 1.07/1.27      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.07/1.27         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 1.07/1.27          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 1.07/1.27      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.07/1.27  thf('11', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 1.07/1.27           = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 1.07/1.27      inference('sup-', [status(thm)], ['9', '10'])).
% 1.07/1.27  thf('12', plain,
% 1.07/1.27      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 1.07/1.27          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.07/1.27      inference('demod', [status(thm)], ['4', '11'])).
% 1.07/1.27  thf('13', plain,
% 1.07/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.27  thf('14', plain,
% 1.07/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.27  thf(dt_k7_subset_1, axiom,
% 1.07/1.27    (![A:$i,B:$i,C:$i]:
% 1.07/1.27     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.07/1.27       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.07/1.27  thf('15', plain,
% 1.07/1.27      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.07/1.27         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 1.07/1.27          | (m1_subset_1 @ (k7_subset_1 @ X18 @ X17 @ X19) @ 
% 1.07/1.27             (k1_zfmisc_1 @ X18)))),
% 1.07/1.27      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 1.07/1.27  thf('16', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.07/1.27          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.27      inference('sup-', [status(thm)], ['14', '15'])).
% 1.07/1.27  thf('17', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.07/1.27           = (k4_xboole_0 @ sk_B @ X0))),
% 1.07/1.27      inference('sup-', [status(thm)], ['1', '2'])).
% 1.07/1.27  thf('18', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 1.07/1.27          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.27      inference('demod', [status(thm)], ['16', '17'])).
% 1.07/1.27  thf(t48_tops_1, axiom,
% 1.07/1.27    (![A:$i]:
% 1.07/1.27     ( ( l1_pre_topc @ A ) =>
% 1.07/1.27       ( ![B:$i]:
% 1.07/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.27           ( ![C:$i]:
% 1.07/1.27             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.27               ( ( r1_tarski @ B @ C ) =>
% 1.07/1.27                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.07/1.27  thf('19', plain,
% 1.07/1.27      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.07/1.27         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.07/1.27          | ~ (r1_tarski @ X27 @ X29)
% 1.07/1.27          | (r1_tarski @ (k1_tops_1 @ X28 @ X27) @ (k1_tops_1 @ X28 @ X29))
% 1.07/1.27          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.07/1.27          | ~ (l1_pre_topc @ X28))),
% 1.07/1.27      inference('cnf', [status(esa)], [t48_tops_1])).
% 1.07/1.27  thf('20', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         (~ (l1_pre_topc @ sk_A)
% 1.07/1.27          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.07/1.27          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 1.07/1.27             (k1_tops_1 @ sk_A @ X1))
% 1.07/1.27          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 1.07/1.27      inference('sup-', [status(thm)], ['18', '19'])).
% 1.07/1.27  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.27  thf('22', plain,
% 1.07/1.27      (![X0 : $i, X1 : $i]:
% 1.07/1.27         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.07/1.27          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 1.07/1.27             (k1_tops_1 @ sk_A @ X1))
% 1.07/1.27          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 1.07/1.27      inference('demod', [status(thm)], ['20', '21'])).
% 1.07/1.27  thf('23', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 1.07/1.27          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 1.07/1.27             (k1_tops_1 @ sk_A @ sk_B)))),
% 1.07/1.27      inference('sup-', [status(thm)], ['13', '22'])).
% 1.07/1.27  thf(t36_xboole_1, axiom,
% 1.07/1.27    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.07/1.27  thf('24', plain,
% 1.07/1.27      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 1.07/1.27      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.07/1.27  thf('25', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 1.07/1.27          (k1_tops_1 @ sk_A @ sk_B))),
% 1.07/1.27      inference('demod', [status(thm)], ['23', '24'])).
% 1.07/1.27  thf('26', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 1.07/1.27          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.27      inference('demod', [status(thm)], ['16', '17'])).
% 1.07/1.27  thf(t44_tops_1, axiom,
% 1.07/1.27    (![A:$i]:
% 1.07/1.27     ( ( l1_pre_topc @ A ) =>
% 1.07/1.27       ( ![B:$i]:
% 1.07/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.27           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.07/1.27  thf('27', plain,
% 1.07/1.27      (![X25 : $i, X26 : $i]:
% 1.07/1.27         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.07/1.27          | (r1_tarski @ (k1_tops_1 @ X26 @ X25) @ X25)
% 1.07/1.27          | ~ (l1_pre_topc @ X26))),
% 1.07/1.27      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.07/1.27  thf('28', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         (~ (l1_pre_topc @ sk_A)
% 1.07/1.27          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 1.07/1.27             (k4_xboole_0 @ sk_B @ X0)))),
% 1.07/1.27      inference('sup-', [status(thm)], ['26', '27'])).
% 1.07/1.27  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.27  thf('30', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 1.07/1.27          (k4_xboole_0 @ sk_B @ X0))),
% 1.07/1.27      inference('demod', [status(thm)], ['28', '29'])).
% 1.07/1.27  thf(t106_xboole_1, axiom,
% 1.07/1.27    (![A:$i,B:$i,C:$i]:
% 1.07/1.27     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.07/1.27       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.07/1.27  thf('31', plain,
% 1.07/1.27      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.07/1.27         ((r1_xboole_0 @ X3 @ X5)
% 1.07/1.27          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 1.07/1.27      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.07/1.27  thf('32', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         (r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X0)),
% 1.07/1.27      inference('sup-', [status(thm)], ['30', '31'])).
% 1.07/1.27  thf('33', plain,
% 1.07/1.27      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.27  thf('34', plain,
% 1.07/1.27      (![X25 : $i, X26 : $i]:
% 1.07/1.27         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.07/1.27          | (r1_tarski @ (k1_tops_1 @ X26 @ X25) @ X25)
% 1.07/1.27          | ~ (l1_pre_topc @ X26))),
% 1.07/1.27      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.07/1.27  thf('35', plain,
% 1.07/1.27      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 1.07/1.27      inference('sup-', [status(thm)], ['33', '34'])).
% 1.07/1.27  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.27  thf('37', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 1.07/1.27      inference('demod', [status(thm)], ['35', '36'])).
% 1.07/1.27  thf(t12_xboole_1, axiom,
% 1.07/1.27    (![A:$i,B:$i]:
% 1.07/1.27     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.07/1.27  thf('38', plain,
% 1.07/1.27      (![X6 : $i, X7 : $i]:
% 1.07/1.27         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.07/1.27      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.07/1.27  thf('39', plain,
% 1.07/1.27      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C) = (sk_C))),
% 1.07/1.27      inference('sup-', [status(thm)], ['37', '38'])).
% 1.07/1.27  thf(t70_xboole_1, axiom,
% 1.07/1.27    (![A:$i,B:$i,C:$i]:
% 1.07/1.27     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.07/1.27            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.07/1.27       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.07/1.27            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.07/1.27  thf('40', plain,
% 1.07/1.27      (![X10 : $i, X11 : $i, X13 : $i]:
% 1.07/1.27         ((r1_xboole_0 @ X10 @ X11)
% 1.07/1.27          | ~ (r1_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X13)))),
% 1.07/1.27      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.07/1.27  thf('41', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         (~ (r1_xboole_0 @ X0 @ sk_C)
% 1.07/1.27          | (r1_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.07/1.27      inference('sup-', [status(thm)], ['39', '40'])).
% 1.07/1.27  thf('42', plain,
% 1.07/1.27      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 1.07/1.27        (k1_tops_1 @ sk_A @ sk_C))),
% 1.07/1.27      inference('sup-', [status(thm)], ['32', '41'])).
% 1.07/1.27  thf(t86_xboole_1, axiom,
% 1.07/1.27    (![A:$i,B:$i,C:$i]:
% 1.07/1.27     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 1.07/1.27       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 1.07/1.27  thf('43', plain,
% 1.07/1.27      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.07/1.27         (~ (r1_tarski @ X14 @ X15)
% 1.07/1.27          | ~ (r1_xboole_0 @ X14 @ X16)
% 1.07/1.27          | (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X16)))),
% 1.07/1.27      inference('cnf', [status(esa)], [t86_xboole_1])).
% 1.07/1.27  thf('44', plain,
% 1.07/1.27      (![X0 : $i]:
% 1.07/1.27         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 1.07/1.27           (k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))
% 1.07/1.27          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 1.07/1.27               X0))),
% 1.07/1.27      inference('sup-', [status(thm)], ['42', '43'])).
% 1.07/1.27  thf('45', plain,
% 1.07/1.27      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 1.07/1.27        (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 1.07/1.27      inference('sup-', [status(thm)], ['25', '44'])).
% 1.07/1.27  thf('46', plain, ($false), inference('demod', [status(thm)], ['12', '45'])).
% 1.07/1.27  
% 1.07/1.27  % SZS output end Refutation
% 1.07/1.27  
% 1.07/1.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
