%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dMkC35Jwqo

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 (  97 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  466 ( 938 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t91_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tops_1 @ B @ A )
             => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t91_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v2_tops_1 @ X7 @ X8 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X8 ) @ X7 ) @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r1_tarski @ X13 @ ( k2_tops_1 @ X14 @ X13 ) )
      | ( v2_tops_1 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t72_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X12 @ ( k2_pre_topc @ X12 @ X11 ) ) @ ( k2_tops_1 @ X12 @ X11 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t72_tops_1])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tops_1 @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k2_tops_1 @ X14 @ X13 ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v3_tops_1 @ X9 @ X10 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X10 @ X9 ) @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( r1_tarski @ X5 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['16','41'])).

thf('43',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['11','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['6','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dMkC35Jwqo
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:25:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 60 iterations in 0.040s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.50  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.22/0.50  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(t91_tops_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ( v3_tops_1 @ B @ A ) =>
% 0.22/0.50             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( l1_pre_topc @ A ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50              ( ( v3_tops_1 @ B @ A ) =>
% 0.22/0.50                ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t91_tops_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d4_tops_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.50             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.50          | ~ (v2_tops_1 @ X7 @ X8)
% 0.22/0.50          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X8) @ X7) @ X8)
% 0.22/0.50          | ~ (l1_pre_topc @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.22/0.50        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.22/0.50        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('6', plain, (~ (v2_tops_1 @ sk_B @ sk_A)),
% 0.22/0.50      inference('clc', [status(thm)], ['4', '5'])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t88_tops_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ( v2_tops_1 @ B @ A ) <=>
% 0.22/0.50             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.50          | ~ (r1_tarski @ X13 @ (k2_tops_1 @ X14 @ X13))
% 0.22/0.50          | (v2_tops_1 @ X13 @ X14)
% 0.22/0.50          | ~ (l1_pre_topc @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v2_tops_1 @ sk_B @ sk_A)
% 0.22/0.50        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (((v2_tops_1 @ sk_B @ sk_A)
% 0.22/0.50        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t72_tops_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( r1_tarski @
% 0.22/0.50             ( k2_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ 
% 0.22/0.50             ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.50          | (r1_tarski @ (k2_tops_1 @ X12 @ (k2_pre_topc @ X12 @ X11)) @ 
% 0.22/0.50             (k2_tops_1 @ X12 @ X11))
% 0.22/0.50          | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [t72_tops_1])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.22/0.50           (k2_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.22/0.50        (k2_tops_1 @ sk_A @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(dt_k2_pre_topc, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( l1_pre_topc @ A ) & 
% 0.22/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.50       ( m1_subset_1 @
% 0.22/0.50         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X3 : $i, X4 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X3)
% 0.22/0.50          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.22/0.50          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.22/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.50  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.50          | ~ (v2_tops_1 @ X13 @ X14)
% 0.22/0.50          | (r1_tarski @ X13 @ (k2_tops_1 @ X14 @ X13))
% 0.22/0.50          | ~ (l1_pre_topc @ X14))),
% 0.22/0.50      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.50           (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.22/0.50        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.50  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d5_tops_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ( v3_tops_1 @ B @ A ) <=>
% 0.22/0.50             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X9 : $i, X10 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.22/0.50          | ~ (v3_tops_1 @ X9 @ X10)
% 0.22/0.50          | (v2_tops_1 @ (k2_pre_topc @ X10 @ X9) @ X10)
% 0.22/0.50          | ~ (l1_pre_topc @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [d5_tops_1])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50        | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.50  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('29', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('30', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.22/0.50        (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.50      inference('demod', [status(thm)], ['23', '24', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t48_pre_topc, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.22/0.50          | (r1_tarski @ X5 @ (k2_pre_topc @ X6 @ X5))
% 0.22/0.50          | ~ (l1_pre_topc @ X6))),
% 0.22/0.50      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.50  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('36', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['34', '35'])).
% 0.22/0.50  thf(t1_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.50       ( r1_tarski @ A @ C ) ))).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.50          | ~ (r1_tarski @ X1 @ X2)
% 0.22/0.50          | (r1_tarski @ X0 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r1_tarski @ sk_B @ X0)
% 0.22/0.50          | ~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['31', '38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.50          | ~ (r1_tarski @ X1 @ X2)
% 0.22/0.50          | (r1_tarski @ X0 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r1_tarski @ sk_B @ X0)
% 0.22/0.50          | ~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.22/0.50               X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.50  thf('42', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['16', '41'])).
% 0.22/0.50  thf('43', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['11', '42'])).
% 0.22/0.50  thf('44', plain, ($false), inference('demod', [status(thm)], ['6', '43'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
