%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0WN7KBI7cJ

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 186 expanded)
%              Number of leaves         :   22 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  449 (1305 expanded)
%              Number of equality atoms :   11 (  24 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_funct_3_type,type,(
    k9_funct_3: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(k7_funct_3_type,type,(
    k7_funct_3: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
   <= ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( v1_finset_1 @ sk_A )
    | ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t100_funct_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( k9_relat_1 @ ( k9_funct_3 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) @ A )
        = ( k1_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X17: $i] :
      ( ( ( k9_relat_1 @ ( k9_funct_3 @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X17 ) ) @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t100_funct_3])).

thf(fc13_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ ( k9_relat_1 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_finset_1 @ X12 )
      | ( v1_finset_1 @ ( k9_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc13_finset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_finset_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k9_funct_3 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k9_funct_3 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(dt_k7_funct_3,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_funct_1 @ ( k7_funct_3 @ A @ B ) )
      & ( v1_relat_1 @ ( k7_funct_3 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k7_funct_3 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_funct_3])).

thf(redefinition_k9_funct_3,axiom,(
    ! [A: $i,B: $i] :
      ( ( k9_funct_3 @ A @ B )
      = ( k7_funct_3 @ A @ B ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k9_funct_3 @ X15 @ X16 )
      = ( k7_funct_3 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_funct_3])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k9_funct_3 @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X6: $i,X8: $i] :
      ( v1_funct_1 @ ( k7_funct_3 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_funct_3])).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k9_funct_3 @ X15 @ X16 )
      = ( k7_funct_3 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_funct_3])).

thf('13',plain,(
    ! [X6: $i,X8: $i] :
      ( v1_funct_1 @ ( k9_funct_3 @ X6 @ X8 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_finset_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','10','13'])).

thf('15',plain,
    ( ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) )
   <= ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( ~ ( v1_finset_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v1_finset_1 @ sk_A )
   <= ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
    ~ ( v1_finset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','20'])).

thf('22',plain,(
    ~ ( v1_finset_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','21'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X2: $i] :
      ( ( ( k9_relat_1 @ X2 @ ( k1_relat_1 @ X2 ) )
        = ( k2_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('24',plain,
    ( ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t15_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_finset_1 @ A )
     => ( v1_finset_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_finset_1 @ X18 )
      | ( v1_finset_1 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t15_finset_1])).

thf(t145_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k9_relat_1 @ B @ A )
        = ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t145_relat_1])).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_finset_1 @ X12 )
      | ( v1_finset_1 @ ( k9_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc13_finset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_finset_1 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_finset_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_finset_1 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_finset_1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_finset_1 @ ( k1_relat_1 @ X1 ) )
      | ( v1_finset_1 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_1 @ sk_A )
        | ~ ( v1_relat_1 @ sk_A )
        | ( v1_finset_1 @ ( k9_relat_1 @ sk_A @ X0 ) ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ! [X0: $i] :
        ( v1_finset_1 @ ( k9_relat_1 @ sk_A @ X0 ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( ( v1_finset_1 @ ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_finset_1 @ ( k2_relat_1 @ sk_A ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) )
    | ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('39',plain,(
    v1_finset_1 @ ( k1_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','20','38'])).

thf('40',plain,(
    v1_finset_1 @ ( k2_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['37','39'])).

thf(fc14_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_finset_1 @ A )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('41',plain,(
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

thf('42',plain,(
    ! [X3: $i] :
      ( ( ( k3_xboole_0 @ X3 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X3 ) @ ( k2_relat_1 @ X3 ) ) )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t22_relat_1])).

thf(fc10_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_finset_1 @ B )
     => ( v1_finset_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_finset_1 @ ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( v1_finset_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc10_finset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_finset_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_finset_1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_finset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( v1_finset_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) )
   <= ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('49',plain,(
    v1_finset_1 @ ( k1_relat_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','20','38'])).

thf('50',plain,(
    v1_finset_1 @ ( k1_relat_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['48','49'])).

thf('51',plain,(
    v1_finset_1 @ sk_A ),
    inference(demod,[status(thm)],['46','47','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['22','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0WN7KBI7cJ
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:41:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 39 iterations in 0.031s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(k9_funct_3_type, type, k9_funct_3: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.20/0.48  thf(k7_funct_3_type, type, k7_funct_3: $i > $i > $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(t29_finset_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48       ( ( v1_finset_1 @ ( k1_relat_1 @ A ) ) <=> ( v1_finset_1 @ A ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48          ( ( v1_finset_1 @ ( k1_relat_1 @ A ) ) <=> ( v1_finset_1 @ A ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t29_finset_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((~ (v1_finset_1 @ sk_A) | ~ (v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((~ (v1_finset_1 @ sk_A)) <= (~ ((v1_finset_1 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (~ ((v1_finset_1 @ sk_A)) | ~ ((v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((v1_finset_1 @ sk_A) | (v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain, (((v1_finset_1 @ sk_A)) <= (((v1_finset_1 @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf(t100_funct_3, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.48       ( ( k9_relat_1 @
% 0.20/0.48           ( k9_funct_3 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) @ A ) =
% 0.20/0.48         ( k1_relat_1 @ A ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X17 : $i]:
% 0.20/0.48         (((k9_relat_1 @ 
% 0.20/0.48            (k9_funct_3 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)) @ X17)
% 0.20/0.48            = (k1_relat_1 @ X17))
% 0.20/0.48          | ~ (v1_funct_1 @ X17)
% 0.20/0.48          | ~ (v1_relat_1 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [t100_funct_3])).
% 0.20/0.48  thf(fc13_finset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v1_finset_1 @ B ) ) =>
% 0.20/0.48       ( v1_finset_1 @ ( k9_relat_1 @ A @ B ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (v1_funct_1 @ X11)
% 0.20/0.48          | ~ (v1_relat_1 @ X11)
% 0.20/0.48          | ~ (v1_finset_1 @ X12)
% 0.20/0.48          | (v1_finset_1 @ (k9_relat_1 @ X11 @ X12)))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc13_finset_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v1_finset_1 @ (k1_relat_1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_funct_1 @ X0)
% 0.20/0.48          | ~ (v1_finset_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ 
% 0.20/0.48               (k9_funct_3 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.20/0.48          | ~ (v1_funct_1 @ 
% 0.20/0.48               (k9_funct_3 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(dt_k7_funct_3, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_funct_1 @ ( k7_funct_3 @ A @ B ) ) & 
% 0.20/0.48       ( v1_relat_1 @ ( k7_funct_3 @ A @ B ) ) ))).
% 0.20/0.48  thf('8', plain, (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k7_funct_3 @ X6 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k7_funct_3])).
% 0.20/0.48  thf(redefinition_k9_funct_3, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k9_funct_3 @ A @ B ) = ( k7_funct_3 @ A @ B ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         ((k9_funct_3 @ X15 @ X16) = (k7_funct_3 @ X15 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k9_funct_3])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k9_funct_3 @ X6 @ X7))),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X6 : $i, X8 : $i]: (v1_funct_1 @ (k7_funct_3 @ X6 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k7_funct_3])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X15 : $i, X16 : $i]:
% 0.20/0.48         ((k9_funct_3 @ X15 @ X16) = (k7_funct_3 @ X15 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k9_funct_3])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X6 : $i, X8 : $i]: (v1_funct_1 @ (k9_funct_3 @ X6 @ X8))),
% 0.20/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v1_finset_1 @ (k1_relat_1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_funct_1 @ X0)
% 0.20/0.48          | ~ (v1_finset_1 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '10', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((~ (v1_finset_1 @ (k1_relat_1 @ sk_A)))
% 0.20/0.48         <= (~ ((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (((~ (v1_finset_1 @ sk_A) | ~ (v1_funct_1 @ sk_A) | ~ (v1_relat_1 @ sk_A)))
% 0.20/0.48         <= (~ ((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      ((~ (v1_finset_1 @ sk_A)) <= (~ ((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (((v1_finset_1 @ (k1_relat_1 @ sk_A))) | ~ ((v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '19'])).
% 0.20/0.48  thf('21', plain, (~ ((v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['2', '20'])).
% 0.20/0.48  thf('22', plain, (~ (v1_finset_1 @ sk_A)),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['1', '21'])).
% 0.20/0.48  thf(t146_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X2 : $i]:
% 0.20/0.48         (((k9_relat_1 @ X2 @ (k1_relat_1 @ X2)) = (k2_relat_1 @ X2))
% 0.20/0.48          | ~ (v1_relat_1 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (((v1_finset_1 @ (k1_relat_1 @ sk_A)))
% 0.20/0.48         <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf(t15_finset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_finset_1 @ A ) => ( v1_finset_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i]:
% 0.20/0.48         (~ (v1_finset_1 @ X18) | (v1_finset_1 @ (k3_xboole_0 @ X18 @ X19)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t15_finset_1])).
% 0.20/0.48  thf(t145_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( k9_relat_1 @ B @ A ) =
% 0.20/0.48         ( k9_relat_1 @ B @ ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k9_relat_1 @ X0 @ X1)
% 0.20/0.48            = (k9_relat_1 @ X0 @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ X1)))
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t145_relat_1])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (v1_funct_1 @ X11)
% 0.20/0.48          | ~ (v1_relat_1 @ X11)
% 0.20/0.48          | ~ (v1_finset_1 @ X12)
% 0.20/0.48          | (v1_finset_1 @ (k9_relat_1 @ X11 @ X12)))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc13_finset_1])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((v1_finset_1 @ (k9_relat_1 @ X1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_finset_1 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_funct_1 @ X1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v1_funct_1 @ X1)
% 0.20/0.48          | ~ (v1_finset_1 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | (v1_finset_1 @ (k9_relat_1 @ X1 @ X0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v1_finset_1 @ (k1_relat_1 @ X1))
% 0.20/0.48          | (v1_finset_1 @ (k9_relat_1 @ X1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_funct_1 @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          (~ (v1_funct_1 @ sk_A)
% 0.20/0.48           | ~ (v1_relat_1 @ sk_A)
% 0.20/0.48           | (v1_finset_1 @ (k9_relat_1 @ sk_A @ X0))))
% 0.20/0.48         <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '30'])).
% 0.20/0.48  thf('32', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      ((![X0 : $i]: (v1_finset_1 @ (k9_relat_1 @ sk_A @ X0)))
% 0.20/0.48         <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((((v1_finset_1 @ (k2_relat_1 @ sk_A)) | ~ (v1_relat_1 @ sk_A)))
% 0.20/0.48         <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['23', '34'])).
% 0.20/0.48  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (((v1_finset_1 @ (k2_relat_1 @ sk_A)))
% 0.20/0.48         <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (((v1_finset_1 @ (k1_relat_1 @ sk_A))) | ((v1_finset_1 @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('39', plain, (((v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['2', '20', '38'])).
% 0.20/0.48  thf('40', plain, ((v1_finset_1 @ (k2_relat_1 @ sk_A))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['37', '39'])).
% 0.20/0.48  thf(fc14_finset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_finset_1 @ A ) & ( v1_finset_1 @ B ) ) =>
% 0.20/0.48       ( v1_finset_1 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i]:
% 0.20/0.48         (~ (v1_finset_1 @ X13)
% 0.20/0.48          | ~ (v1_finset_1 @ X14)
% 0.20/0.48          | (v1_finset_1 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc14_finset_1])).
% 0.20/0.48  thf(t22_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( k3_xboole_0 @
% 0.20/0.48           A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) =
% 0.20/0.48         ( A ) ) ))).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X3 : $i]:
% 0.20/0.48         (((k3_xboole_0 @ X3 @ 
% 0.20/0.48            (k2_zfmisc_1 @ (k1_relat_1 @ X3) @ (k2_relat_1 @ X3))) = (X3))
% 0.20/0.48          | ~ (v1_relat_1 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t22_relat_1])).
% 0.20/0.48  thf(fc10_finset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_finset_1 @ B ) => ( v1_finset_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         ((v1_finset_1 @ (k3_xboole_0 @ X9 @ X10)) | ~ (v1_finset_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc10_finset_1])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v1_finset_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_finset_1 @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_finset_1 @ (k2_relat_1 @ X0))
% 0.20/0.48          | ~ (v1_finset_1 @ (k1_relat_1 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | (v1_finset_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['41', '44'])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (((v1_finset_1 @ sk_A)
% 0.20/0.48        | ~ (v1_relat_1 @ sk_A)
% 0.20/0.48        | ~ (v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['40', '45'])).
% 0.20/0.48  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (((v1_finset_1 @ (k1_relat_1 @ sk_A)))
% 0.20/0.48         <= (((v1_finset_1 @ (k1_relat_1 @ sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('49', plain, (((v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['2', '20', '38'])).
% 0.20/0.48  thf('50', plain, ((v1_finset_1 @ (k1_relat_1 @ sk_A))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['48', '49'])).
% 0.20/0.48  thf('51', plain, ((v1_finset_1 @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['46', '47', '50'])).
% 0.20/0.48  thf('52', plain, ($false), inference('demod', [status(thm)], ['22', '51'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
