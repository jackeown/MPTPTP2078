%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ijDYY9WxPw

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 112 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  640 (1331 expanded)
%              Number of equality atoms :   24 (  57 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t102_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
           => ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
              = ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v5_tops_1 @ B @ A )
             => ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
                = ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t102_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t72_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X18 @ ( k2_pre_topc @ X18 @ X17 ) ) @ ( k2_tops_1 @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_tops_1 @ X16 @ X15 )
        = ( k2_tops_1 @ X16 @ ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k1_tops_1 @ X10 @ X9 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k2_pre_topc @ X10 @ ( k3_subset_1 @ ( u1_struct_0 @ X10 ) @ X9 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_tops_1 @ X16 @ X15 )
        = ( k2_tops_1 @ X16 @ ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('26',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['22','23','26'])).

thf('28',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['4','5','19','27'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X18 @ ( k2_pre_topc @ X18 @ X17 ) ) @ ( k2_tops_1 @ X18 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
          <=> ( B
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v5_tops_1 @ X11 @ X12 )
      | ( X11
        = ( k2_pre_topc @ X12 @ ( k1_tops_1 @ X12 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['32','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ijDYY9WxPw
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 109 iterations in 0.098s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.52  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.19/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.19/0.52  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.19/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.52  thf(t102_tops_1, conjecture,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( l1_pre_topc @ A ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52           ( ( v5_tops_1 @ B @ A ) =>
% 0.19/0.52             ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) =
% 0.19/0.52               ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i]:
% 0.19/0.52        ( ( l1_pre_topc @ A ) =>
% 0.19/0.52          ( ![B:$i]:
% 0.19/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52              ( ( v5_tops_1 @ B @ A ) =>
% 0.19/0.52                ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) =
% 0.19/0.52                  ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t102_tops_1])).
% 0.19/0.52  thf('0', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(dt_k3_subset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.52       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.52  thf('1', plain,
% 0.19/0.52      (![X3 : $i, X4 : $i]:
% 0.19/0.52         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 0.19/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.19/0.52      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.19/0.52  thf('2', plain,
% 0.19/0.52      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.52  thf(t72_tops_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( l1_pre_topc @ A ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52           ( r1_tarski @
% 0.19/0.52             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 0.19/0.52             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      (![X17 : $i, X18 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.19/0.52          | (r1_tarski @ (k2_tops_1 @ X18 @ (k2_pre_topc @ X18 @ X17)) @ 
% 0.19/0.52             (k2_tops_1 @ X18 @ X17))
% 0.19/0.52          | ~ (l1_pre_topc @ X18))),
% 0.19/0.52      inference('cnf', [status(esa)], [t72_tops_1])).
% 0.19/0.52  thf('4', plain,
% 0.19/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.52        | (r1_tarski @ 
% 0.19/0.52           (k2_tops_1 @ sk_A @ 
% 0.19/0.52            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 0.19/0.52           (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.52  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.52  thf(dt_k2_pre_topc, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( l1_pre_topc @ A ) & 
% 0.19/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.52       ( m1_subset_1 @
% 0.19/0.52         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      (![X7 : $i, X8 : $i]:
% 0.19/0.52         (~ (l1_pre_topc @ X7)
% 0.19/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.19/0.52          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 0.19/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.19/0.52      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.19/0.52  thf('8', plain,
% 0.19/0.52      (((m1_subset_1 @ 
% 0.19/0.52         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.19/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.52  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('10', plain,
% 0.19/0.52      ((m1_subset_1 @ 
% 0.19/0.52        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.19/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.52  thf(t62_tops_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( l1_pre_topc @ A ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52           ( ( k2_tops_1 @ A @ B ) =
% 0.19/0.52             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.19/0.52  thf('11', plain,
% 0.19/0.52      (![X15 : $i, X16 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.52          | ((k2_tops_1 @ X16 @ X15)
% 0.19/0.52              = (k2_tops_1 @ X16 @ (k3_subset_1 @ (u1_struct_0 @ X16) @ X15)))
% 0.19/0.52          | ~ (l1_pre_topc @ X16))),
% 0.19/0.52      inference('cnf', [status(esa)], [t62_tops_1])).
% 0.19/0.52  thf('12', plain,
% 0.19/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.52        | ((k2_tops_1 @ sk_A @ 
% 0.19/0.52            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.52            = (k2_tops_1 @ sk_A @ 
% 0.19/0.52               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.52                (k2_pre_topc @ sk_A @ 
% 0.19/0.52                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.52  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('14', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(d1_tops_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( l1_pre_topc @ A ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52           ( ( k1_tops_1 @ A @ B ) =
% 0.19/0.52             ( k3_subset_1 @
% 0.19/0.52               ( u1_struct_0 @ A ) @ 
% 0.19/0.52               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.19/0.52  thf('15', plain,
% 0.19/0.52      (![X9 : $i, X10 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.19/0.52          | ((k1_tops_1 @ X10 @ X9)
% 0.19/0.52              = (k3_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.19/0.52                 (k2_pre_topc @ X10 @ (k3_subset_1 @ (u1_struct_0 @ X10) @ X9))))
% 0.19/0.52          | ~ (l1_pre_topc @ X10))),
% 0.19/0.52      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.19/0.52  thf('16', plain,
% 0.19/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.52        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.19/0.52            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.52               (k2_pre_topc @ sk_A @ 
% 0.19/0.52                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.52  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('18', plain,
% 0.19/0.52      (((k1_tops_1 @ sk_A @ sk_B)
% 0.19/0.52         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.52            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.19/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.52  thf('19', plain,
% 0.19/0.52      (((k2_tops_1 @ sk_A @ 
% 0.19/0.52         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.52         = (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.52      inference('demod', [status(thm)], ['12', '13', '18'])).
% 0.19/0.52  thf('20', plain,
% 0.19/0.52      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.52  thf('21', plain,
% 0.19/0.52      (![X15 : $i, X16 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.52          | ((k2_tops_1 @ X16 @ X15)
% 0.19/0.52              = (k2_tops_1 @ X16 @ (k3_subset_1 @ (u1_struct_0 @ X16) @ X15)))
% 0.19/0.52          | ~ (l1_pre_topc @ X16))),
% 0.19/0.52      inference('cnf', [status(esa)], [t62_tops_1])).
% 0.19/0.52  thf('22', plain,
% 0.19/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.52        | ((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.52            = (k2_tops_1 @ sk_A @ 
% 0.19/0.52               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.52                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.52  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('24', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(involutiveness_k3_subset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.52       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.19/0.52  thf('25', plain,
% 0.19/0.52      (![X5 : $i, X6 : $i]:
% 0.19/0.52         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 0.19/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.19/0.52      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.19/0.52  thf('26', plain,
% 0.19/0.52      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.52         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.19/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.52  thf('27', plain,
% 0.19/0.52      (((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.19/0.52         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.19/0.52      inference('demod', [status(thm)], ['22', '23', '26'])).
% 0.19/0.52  thf('28', plain,
% 0.19/0.52      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.19/0.52        (k2_tops_1 @ sk_A @ sk_B))),
% 0.19/0.52      inference('demod', [status(thm)], ['4', '5', '19', '27'])).
% 0.19/0.52  thf(d10_xboole_0, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.52  thf('29', plain,
% 0.19/0.52      (![X0 : $i, X2 : $i]:
% 0.19/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.52  thf('30', plain,
% 0.19/0.52      ((~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.19/0.52           (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.19/0.52        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.19/0.52            = (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.52  thf('31', plain,
% 0.19/0.52      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.19/0.52         != (k2_tops_1 @ sk_A @ sk_B))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('32', plain,
% 0.19/0.52      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.19/0.52          (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.52      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.19/0.52  thf('33', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(dt_k1_tops_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( l1_pre_topc @ A ) & 
% 0.19/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.52       ( m1_subset_1 @
% 0.19/0.52         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.52  thf('34', plain,
% 0.19/0.52      (![X13 : $i, X14 : $i]:
% 0.19/0.52         (~ (l1_pre_topc @ X13)
% 0.19/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.19/0.52          | (m1_subset_1 @ (k1_tops_1 @ X13 @ X14) @ 
% 0.19/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 0.19/0.52      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.19/0.52  thf('35', plain,
% 0.19/0.52      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.19/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.52  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('37', plain,
% 0.19/0.52      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.19/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.19/0.52  thf('38', plain,
% 0.19/0.52      (![X17 : $i, X18 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.19/0.52          | (r1_tarski @ (k2_tops_1 @ X18 @ (k2_pre_topc @ X18 @ X17)) @ 
% 0.19/0.52             (k2_tops_1 @ X18 @ X17))
% 0.19/0.52          | ~ (l1_pre_topc @ X18))),
% 0.19/0.52      inference('cnf', [status(esa)], [t72_tops_1])).
% 0.19/0.52  thf('39', plain,
% 0.19/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.52        | (r1_tarski @ 
% 0.19/0.52           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.19/0.52           (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.52  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('41', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(d7_tops_1, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ( l1_pre_topc @ A ) =>
% 0.19/0.52       ( ![B:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.52           ( ( v5_tops_1 @ B @ A ) <=>
% 0.19/0.52             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.52  thf('42', plain,
% 0.19/0.52      (![X11 : $i, X12 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.19/0.52          | ~ (v5_tops_1 @ X11 @ X12)
% 0.19/0.52          | ((X11) = (k2_pre_topc @ X12 @ (k1_tops_1 @ X12 @ X11)))
% 0.19/0.52          | ~ (l1_pre_topc @ X12))),
% 0.19/0.52      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.19/0.52  thf('43', plain,
% 0.19/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.52        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.19/0.52        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.52  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('45', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('46', plain,
% 0.19/0.52      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.52      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.19/0.52  thf('47', plain,
% 0.19/0.52      ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.19/0.52        (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.19/0.52      inference('demod', [status(thm)], ['39', '40', '46'])).
% 0.19/0.52  thf('48', plain, ($false), inference('demod', [status(thm)], ['32', '47'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
