%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jxyzqD9ji6

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 (  92 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  387 ( 632 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_funct_3_type,type,(
    k9_funct_3: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t29_finset_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_finset_1 @ ( k1_relat_1 @ A ) )
      <=> ( v1_finset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_finset_1 @ ( k1_relat_1 @ A ) )
        <=> ( v1_finset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_finset_1])).

thf('0',plain,
    ( ~ ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_finset_1 @ sk_A )
    | ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t26_finset_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_finset_1 @ ( k1_relat_1 @ A ) )
       => ( v1_finset_1 @ ( k2_relat_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X16: $i] :
      ( ~ ( v1_finset_1 @ ( k1_relat_1 @ X16 ) )
      | ( v1_finset_1 @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t26_finset_1])).

thf('5',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( v1_finset_1 @ ( k2_relat_1 @ sk_A ) ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v1_finset_1 @ ( k2_relat_1 @ sk_A ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(fc14_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_finset_1 @ A )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_finset_1 @ X13 )
      | ~ ( v1_finset_1 @ X14 )
      | ( v1_finset_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fc14_finset_1])).

thf(t22_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( ( k3_xboole_0 @ X4 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X4 ) @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf(fc10_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_finset_1 @ B )
     => ( v1_finset_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_finset_1 @ ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( v1_finset_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc10_finset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_finset_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_finset_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_finset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( ( v1_finset_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ~ ( v1_finset_1 @ sk_A )
   <= ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_finset_1 @ sk_A )
    | ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('21',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(t100_funct_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( k9_relat_1 @ ( k9_funct_3 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) @ A )
        = ( k1_relat_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X15: $i] :
      ( ( ( k9_relat_1 @ ( k9_funct_3 @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X15 ) ) @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t100_funct_3])).

thf(fc13_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ ( k9_relat_1 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_finset_1 @ X12 )
      | ( v1_finset_1 @ ( k9_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc13_finset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_finset_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k9_funct_3 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k9_funct_3 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(dt_k9_funct_3,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( k9_funct_3 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ A ) ) )
      & ( v1_funct_2 @ ( k9_funct_3 @ A @ B ) @ ( k2_zfmisc_1 @ A @ B ) @ A )
      & ( v1_funct_1 @ ( k9_funct_3 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_funct_1 @ ( k9_funct_3 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k9_funct_3])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_finset_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k9_funct_3 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X5: $i,X8: $i] :
      ( m1_subset_1 @ ( k9_funct_3 @ X5 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X8 ) @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_funct_3])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X0 ) )
      | ( v1_relat_1 @ ( k9_funct_3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k9_funct_3 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_finset_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,
    ( ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( ~ ( v1_finset_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v1_finset_1 @ sk_A )
   <= ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ~ ( v1_finset_1 @ sk_A )
    | ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','37'])).

thf('39',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','19','20','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jxyzqD9ji6
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:33:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 27 iterations in 0.016s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.22/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(k9_funct_3_type, type, k9_funct_3: $i > $i > $i).
% 0.22/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.51  thf(t29_finset_1, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.51       ( ( v1_finset_1 @ ( k1_relat_1 @ A ) ) <=> ( v1_finset_1 @ A ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.51          ( ( v1_finset_1 @ ( k1_relat_1 @ A ) ) <=> ( v1_finset_1 @ A ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t29_finset_1])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      ((~ (v1_finset_1 @ sk_A) | ~ (v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (~ ((v1_finset_1 @ sk_A)) | ~ ((v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (((v1_finset_1 @ sk_A) | (v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (((v1_finset_1 @ (k1_relat_1 @ sk_A)))
% 0.22/0.51         <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf(t26_finset_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.51       ( ( v1_finset_1 @ ( k1_relat_1 @ A ) ) =>
% 0.22/0.51         ( v1_finset_1 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X16 : $i]:
% 0.22/0.51         (~ (v1_finset_1 @ (k1_relat_1 @ X16))
% 0.22/0.51          | (v1_finset_1 @ (k2_relat_1 @ X16))
% 0.22/0.51          | ~ (v1_funct_1 @ X16)
% 0.22/0.51          | ~ (v1_relat_1 @ X16))),
% 0.22/0.51      inference('cnf', [status(esa)], [t26_finset_1])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (((~ (v1_relat_1 @ sk_A)
% 0.22/0.51         | ~ (v1_funct_1 @ sk_A)
% 0.22/0.51         | (v1_finset_1 @ (k2_relat_1 @ sk_A))))
% 0.22/0.51         <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('7', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (((v1_finset_1 @ (k2_relat_1 @ sk_A)))
% 0.22/0.51         <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.22/0.51  thf(fc14_finset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( v1_finset_1 @ A ) & ( v1_finset_1 @ B ) ) =>
% 0.22/0.51       ( v1_finset_1 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X13 : $i, X14 : $i]:
% 0.22/0.51         (~ (v1_finset_1 @ X13)
% 0.22/0.51          | ~ (v1_finset_1 @ X14)
% 0.22/0.51          | (v1_finset_1 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.22/0.51      inference('cnf', [status(esa)], [fc14_finset_1])).
% 0.22/0.51  thf(t22_relat_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( ( k3_xboole_0 @
% 0.22/0.51           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.22/0.51         ( A ) ) ))).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X4 : $i]:
% 0.22/0.51         (((k3_xboole_0 @ X4 @ 
% 0.22/0.51            (k2_zfmisc_1 @ (k1_relat_1 @ X4) @ (k2_relat_1 @ X4))) = (X4))
% 0.22/0.51          | ~ (v1_relat_1 @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.22/0.51  thf(fc10_finset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( v1_finset_1 @ B ) => ( v1_finset_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X9 : $i, X10 : $i]:
% 0.22/0.51         ((v1_finset_1 @ (k3_xboole_0 @ X9 @ X10)) | ~ (v1_finset_1 @ X10))),
% 0.22/0.51      inference('cnf', [status(esa)], [fc10_finset_1])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v1_finset_1 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_finset_1 @ 
% 0.22/0.51               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.22/0.51      inference('sup+', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_finset_1 @ (k2_relat_1 @ X0))
% 0.22/0.51          | ~ (v1_finset_1 @ (k1_relat_1 @ X0))
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | (v1_finset_1 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['9', '12'])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      ((((v1_finset_1 @ sk_A)
% 0.22/0.51         | ~ (v1_relat_1 @ sk_A)
% 0.22/0.51         | ~ (v1_finset_1 @ (k1_relat_1 @ sk_A))))
% 0.22/0.51         <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['8', '13'])).
% 0.22/0.51  thf('15', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (((v1_finset_1 @ (k1_relat_1 @ sk_A)))
% 0.22/0.51         <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (((v1_finset_1 @ sk_A)) <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.22/0.51  thf('18', plain, ((~ (v1_finset_1 @ sk_A)) <= (~ ((v1_finset_1 @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (((v1_finset_1 @ sk_A)) | ~ ((v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (((v1_finset_1 @ sk_A)) | ((v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf('21', plain, (((v1_finset_1 @ sk_A)) <= (((v1_finset_1 @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['2'])).
% 0.22/0.51  thf(t100_funct_3, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.51       ( ( k9_relat_1 @
% 0.22/0.51           ( k9_funct_3 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) @ A ) =
% 0.22/0.51         ( k1_relat_1 @ A ) ) ))).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X15 : $i]:
% 0.22/0.51         (((k9_relat_1 @ 
% 0.22/0.51            (k9_funct_3 @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X15)) @ X15)
% 0.22/0.51            = (k1_relat_1 @ X15))
% 0.22/0.51          | ~ (v1_funct_1 @ X15)
% 0.22/0.51          | ~ (v1_relat_1 @ X15))),
% 0.22/0.51      inference('cnf', [status(esa)], [t100_funct_3])).
% 0.22/0.51  thf(fc13_finset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_finset_1 @ B ) ) =>
% 0.22/0.51       ( v1_finset_1 @ ( k9_relat_1 @ A @ B ) ) ))).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X11 : $i, X12 : $i]:
% 0.22/0.51         (~ (v1_funct_1 @ X11)
% 0.22/0.51          | ~ (v1_relat_1 @ X11)
% 0.22/0.51          | ~ (v1_finset_1 @ X12)
% 0.22/0.51          | (v1_finset_1 @ (k9_relat_1 @ X11 @ X12)))),
% 0.22/0.51      inference('cnf', [status(esa)], [fc13_finset_1])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v1_finset_1 @ (k1_relat_1 @ X0))
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_funct_1 @ X0)
% 0.22/0.51          | ~ (v1_finset_1 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ 
% 0.22/0.51               (k9_funct_3 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.22/0.51          | ~ (v1_funct_1 @ 
% 0.22/0.51               (k9_funct_3 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.22/0.51      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf(dt_k9_funct_3, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( m1_subset_1 @
% 0.22/0.51         ( k9_funct_3 @ A @ B ) @ 
% 0.22/0.51         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ A ) ) ) & 
% 0.22/0.51       ( v1_funct_2 @ ( k9_funct_3 @ A @ B ) @ ( k2_zfmisc_1 @ A @ B ) @ A ) & 
% 0.22/0.51       ( v1_funct_1 @ ( k9_funct_3 @ A @ B ) ) ))).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (![X5 : $i, X6 : $i]: (v1_funct_1 @ (k9_funct_3 @ X5 @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k9_funct_3])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v1_finset_1 @ (k1_relat_1 @ X0))
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_funct_1 @ X0)
% 0.22/0.51          | ~ (v1_finset_1 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ 
% 0.22/0.51               (k9_funct_3 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.22/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (![X5 : $i, X8 : $i]:
% 0.22/0.51         (m1_subset_1 @ (k9_funct_3 @ X5 @ X8) @ 
% 0.22/0.51          (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X8) @ X5)))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k9_funct_3])).
% 0.22/0.51  thf(cc2_relat_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.22/0.51          | (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X0))
% 0.22/0.51          | (v1_relat_1 @ (k9_funct_3 @ X0 @ X1)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.51  thf(fc6_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k9_funct_3 @ X0 @ X1))),
% 0.22/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((v1_finset_1 @ (k1_relat_1 @ X0))
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_funct_1 @ X0)
% 0.22/0.51          | ~ (v1_finset_1 @ X0))),
% 0.22/0.51      inference('demod', [status(thm)], ['26', '31'])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      ((~ (v1_finset_1 @ (k1_relat_1 @ sk_A)))
% 0.22/0.51         <= (~ ((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (((~ (v1_finset_1 @ sk_A) | ~ (v1_funct_1 @ sk_A) | ~ (v1_relat_1 @ sk_A)))
% 0.22/0.51         <= (~ ((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.51  thf('35', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      ((~ (v1_finset_1 @ sk_A)) <= (~ ((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      (~ ((v1_finset_1 @ sk_A)) | ((v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['21', '37'])).
% 0.22/0.51  thf('39', plain, ($false),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['1', '19', '20', '38'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
