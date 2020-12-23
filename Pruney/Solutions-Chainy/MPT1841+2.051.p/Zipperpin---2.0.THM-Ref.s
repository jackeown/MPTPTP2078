%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jN6vw6Wfqz

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 102 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :  382 ( 697 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t6_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
                & ( v1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tex_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['1','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_zfmisc_1 @ X15 )
      | ( X16 = X15 )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = sk_A )
    | ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ X4 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_B_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['24','27'])).

thf('29',plain,(
    v1_subset_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['7','28'])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( sk_B @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( sk_B @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_zfmisc_1 @ X15 )
      | ( X16 = X15 )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( sk_B @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf(cc2_subset_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_subset_1 @ B @ A )
           => ~ ( v1_xboole_0 @ B ) ) ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( v1_xboole_0 @ X5 )
      | ( v1_subset_1 @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_xboole_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( sk_B @ X0 )
        = X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','43'])).

thf('45',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jN6vw6Wfqz
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:12:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 41 iterations in 0.021s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(t6_tex_2, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.48           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.22/0.48                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.48              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.22/0.48                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.22/0.48  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.48       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X13 : $i, X14 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ X13)
% 0.22/0.48          | ~ (m1_subset_1 @ X14 @ X13)
% 0.22/0.48          | ((k6_domain_1 @ X13 @ X14) = (k1_tarski @ X14)))),
% 0.22/0.48      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      ((((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.22/0.48        | (v1_xboole_0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf('5', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('6', plain, (((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))),
% 0.22/0.48      inference('clc', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf('7', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.22/0.48      inference('demod', [status(thm)], ['1', '6'])).
% 0.22/0.48  thf('8', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(dt_k6_domain_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.48       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X11 : $i, X12 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ X11)
% 0.22/0.48          | ~ (m1_subset_1 @ X12 @ X11)
% 0.22/0.48          | (m1_subset_1 @ (k6_domain_1 @ X11 @ X12) @ (k1_zfmisc_1 @ X11)))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (((m1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.48        | (v1_xboole_0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.48  thf('11', plain, (((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))),
% 0.22/0.48      inference('clc', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.48        | (v1_xboole_0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('13', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      ((m1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.48      inference('clc', [status(thm)], ['12', '13'])).
% 0.22/0.48  thf(t3_subset, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X8 : $i, X9 : $i]:
% 0.22/0.48         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.48  thf('16', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.22/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.48  thf(t1_tex_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.22/0.48           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (![X15 : $i, X16 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ X15)
% 0.22/0.48          | ~ (v1_zfmisc_1 @ X15)
% 0.22/0.48          | ((X16) = (X15))
% 0.22/0.48          | ~ (r1_tarski @ X16 @ X15)
% 0.22/0.48          | (v1_xboole_0 @ X16))),
% 0.22/0.48      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.22/0.48        | ((k1_tarski @ sk_B_1) = (sk_A))
% 0.22/0.48        | ~ (v1_zfmisc_1 @ sk_A)
% 0.22/0.48        | (v1_xboole_0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.48  thf('19', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.22/0.48        | ((k1_tarski @ sk_B_1) = (sk_A))
% 0.22/0.48        | (v1_xboole_0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf('21', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      ((((k1_tarski @ sk_B_1) = (sk_A)) | (v1_xboole_0 @ (k1_tarski @ sk_B_1)))),
% 0.22/0.48      inference('clc', [status(thm)], ['20', '21'])).
% 0.22/0.48  thf(l13_xboole_0, axiom,
% 0.22/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.48  thf('24', plain,
% 0.22/0.48      ((((k1_tarski @ sk_B_1) = (sk_A))
% 0.22/0.48        | ((k1_tarski @ sk_B_1) = (k1_xboole_0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.48  thf(t1_boole, axiom,
% 0.22/0.48    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.48  thf('25', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.48  thf(t49_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.22/0.48  thf('26', plain,
% 0.22/0.48      (![X3 : $i, X4 : $i]:
% 0.22/0.48         ((k2_xboole_0 @ (k1_tarski @ X3) @ X4) != (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.22/0.48  thf('27', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.48  thf('28', plain, (((k1_tarski @ sk_B_1) = (sk_A))),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['24', '27'])).
% 0.22/0.48  thf('29', plain, ((v1_subset_1 @ sk_A @ sk_A)),
% 0.22/0.48      inference('demod', [status(thm)], ['7', '28'])).
% 0.22/0.48  thf(rc3_subset_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ?[B:$i]:
% 0.22/0.48       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.22/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.22/0.48  thf('30', plain,
% 0.22/0.48      (![X7 : $i]: (m1_subset_1 @ (sk_B @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.22/0.48      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.22/0.48  thf('31', plain,
% 0.22/0.48      (![X8 : $i, X9 : $i]:
% 0.22/0.48         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.48  thf('32', plain, (![X0 : $i]: (r1_tarski @ (sk_B @ X0) @ X0)),
% 0.22/0.48      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.48  thf('33', plain,
% 0.22/0.48      (![X15 : $i, X16 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ X15)
% 0.22/0.48          | ~ (v1_zfmisc_1 @ X15)
% 0.22/0.48          | ((X16) = (X15))
% 0.22/0.48          | ~ (r1_tarski @ X16 @ X15)
% 0.22/0.48          | (v1_xboole_0 @ X16))),
% 0.22/0.48      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.22/0.48  thf('34', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ (sk_B @ X0))
% 0.22/0.48          | ((sk_B @ X0) = (X0))
% 0.22/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.48          | (v1_xboole_0 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.48  thf('35', plain,
% 0.22/0.48      (![X7 : $i]: (m1_subset_1 @ (sk_B @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.22/0.48      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.22/0.48  thf(cc2_subset_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.48           ( ( ~( v1_subset_1 @ B @ A ) ) => ( ~( v1_xboole_0 @ B ) ) ) ) ) ))).
% 0.22/0.48  thf('36', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.22/0.48          | ~ (v1_xboole_0 @ X5)
% 0.22/0.48          | (v1_subset_1 @ X5 @ X6)
% 0.22/0.48          | (v1_xboole_0 @ X6))),
% 0.22/0.48      inference('cnf', [status(esa)], [cc2_subset_1])).
% 0.22/0.48  thf('37', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ X0)
% 0.22/0.48          | (v1_subset_1 @ (sk_B @ X0) @ X0)
% 0.22/0.48          | ~ (v1_xboole_0 @ (sk_B @ X0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.48  thf('38', plain, (![X7 : $i]: ~ (v1_subset_1 @ (sk_B @ X7) @ X7)),
% 0.22/0.48      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.22/0.48  thf('39', plain,
% 0.22/0.48      (![X0 : $i]: (~ (v1_xboole_0 @ (sk_B @ X0)) | (v1_xboole_0 @ X0))),
% 0.22/0.48      inference('clc', [status(thm)], ['37', '38'])).
% 0.22/0.48  thf('40', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ X0)
% 0.22/0.48          | ~ (v1_zfmisc_1 @ X0)
% 0.22/0.48          | ((sk_B @ X0) = (X0))
% 0.22/0.48          | (v1_xboole_0 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['34', '39'])).
% 0.22/0.48  thf('41', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((sk_B @ X0) = (X0)) | ~ (v1_zfmisc_1 @ X0) | (v1_xboole_0 @ X0))),
% 0.22/0.48      inference('simplify', [status(thm)], ['40'])).
% 0.22/0.48  thf('42', plain, (![X7 : $i]: ~ (v1_subset_1 @ (sk_B @ X7) @ X7)),
% 0.22/0.48      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.22/0.48  thf('43', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (v1_subset_1 @ X0 @ X0) | (v1_xboole_0 @ X0) | ~ (v1_zfmisc_1 @ X0))),
% 0.22/0.48      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.48  thf('44', plain, ((~ (v1_zfmisc_1 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['29', '43'])).
% 0.22/0.48  thf('45', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('46', plain, ((v1_xboole_0 @ sk_A)),
% 0.22/0.48      inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.48  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
