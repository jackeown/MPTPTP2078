%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CzTbw0pY3c

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 109 expanded)
%              Number of leaves         :   21 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  312 ( 616 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t45_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v5_ordinal1 @ k1_xboole_0 )
        & ( v1_funct_1 @ k1_xboole_0 )
        & ( v5_relat_1 @ k1_xboole_0 @ A )
        & ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t45_ordinal1])).

thf('0',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
   <= ~ ( v5_ordinal1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t206_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ B )
      & ( v4_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t206_relat_1])).

thf('3',plain,
    ( ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A )
   <= ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v5_relat_1 @ k1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t137_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( ( ( k8_relat_1 @ k1_xboole_0 @ X10 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t137_relat_1])).

thf(fc24_relat_1,axiom,(
    ! [A: $i] :
      ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X16: $i] :
      ( v5_relat_1 @ ( k6_relat_1 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[fc24_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( ( k8_relat_1 @ X9 @ X8 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_xboole_0
      = ( k6_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('19',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
   <= ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X18: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,(
    ~ ( v5_ordinal1 @ k1_xboole_0 ) ),
    inference('sat_resolution*',[status(thm)],['4','21','26','27'])).

thf('29',plain,(
    ~ ( v5_ordinal1 @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf('30',plain,(
    ! [X10: $i] :
      ( ( ( k8_relat_1 @ k1_xboole_0 @ X10 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t137_relat_1])).

thf(rc3_ordinal1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v5_ordinal1 @ B )
      & ( v1_funct_1 @ B )
      & ( v5_relat_1 @ B @ A )
      & ( v1_relat_1 @ B ) ) )).

thf('31',plain,(
    ! [X22: $i] :
      ( v5_relat_1 @ ( sk_B @ X22 ) @ X22 ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( sk_B @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( ( k8_relat_1 @ X9 @ X8 )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( k8_relat_1 @ X0 @ ( sk_B @ X0 ) )
        = ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( sk_B @ X0 ) )
      = ( sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_xboole_0
      = ( sk_B @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X22: $i] :
      ( v1_relat_1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('42',plain,
    ( k1_xboole_0
    = ( sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X22: $i] :
      ( v5_ordinal1 @ ( sk_B @ X22 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('44',plain,(
    v5_ordinal1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['29','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CzTbw0pY3c
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 54 iterations in 0.028s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.50  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(t45_ordinal1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.20/0.50       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.20/0.50          ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t45_ordinal1])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((~ (v5_ordinal1 @ k1_xboole_0)
% 0.20/0.50        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.50        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.50        | ~ (v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((~ (v5_ordinal1 @ k1_xboole_0)) <= (~ ((v5_ordinal1 @ k1_xboole_0)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf(t206_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v5_relat_1 @ k1_xboole_0 @ B ) & ( v4_relat_1 @ k1_xboole_0 @ A ) ))).
% 0.20/0.50  thf('2', plain, (![X11 : $i]: (v5_relat_1 @ k1_xboole_0 @ X11)),
% 0.20/0.50      inference('cnf', [status(esa)], [t206_relat_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      ((~ (v5_relat_1 @ k1_xboole_0 @ sk_A))
% 0.20/0.50         <= (~ ((v5_relat_1 @ k1_xboole_0 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('4', plain, (((v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf(t137_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ( k8_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         (((k8_relat_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [t137_relat_1])).
% 0.20/0.50  thf(fc24_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v5_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.20/0.50       ( v4_relat_1 @ ( k6_relat_1 @ A ) @ A ) & 
% 0.20/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.50  thf('6', plain, (![X16 : $i]: (v5_relat_1 @ (k6_relat_1 @ X16) @ X16)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc24_relat_1])).
% 0.20/0.50  thf(d19_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v5_relat_1 @ X0 @ X1)
% 0.20/0.50          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.50          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.50  thf('9', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ X0)),
% 0.20/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf(t125_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.50         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.20/0.50          | ((k8_relat_1 @ X9 @ X8) = (X8))
% 0.20/0.50          | ~ (v1_relat_1 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.50          | ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))
% 0.20/0.50        | ~ (v1_relat_1 @ (k6_relat_1 @ k1_xboole_0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['5', '14'])).
% 0.20/0.50  thf('16', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.50  thf('17', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.50  thf('19', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.50      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ k1_xboole_0)) <= (~ ((v1_relat_1 @ k1_xboole_0)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('21', plain, (((v1_relat_1 @ k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf(fc3_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.50  thf('23', plain, (![X18 : $i]: (v1_funct_1 @ (k6_relat_1 @ X18))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.50  thf('24', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.50      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((~ (v1_funct_1 @ k1_xboole_0)) <= (~ ((v1_funct_1 @ k1_xboole_0)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('26', plain, (((v1_funct_1 @ k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (~ ((v5_ordinal1 @ k1_xboole_0)) | ~ ((v1_funct_1 @ k1_xboole_0)) | 
% 0.20/0.50       ~ ((v1_relat_1 @ k1_xboole_0)) | ~ ((v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('28', plain, (~ ((v5_ordinal1 @ k1_xboole_0))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['4', '21', '26', '27'])).
% 0.20/0.50  thf('29', plain, (~ (v5_ordinal1 @ k1_xboole_0)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['1', '28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         (((k8_relat_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [t137_relat_1])).
% 0.20/0.50  thf(rc3_ordinal1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ?[B:$i]:
% 0.20/0.50       ( ( v5_ordinal1 @ B ) & ( v1_funct_1 @ B ) & ( v5_relat_1 @ B @ A ) & 
% 0.20/0.50         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.50  thf('31', plain, (![X22 : $i]: (v5_relat_1 @ (sk_B @ X22) @ X22)),
% 0.20/0.50      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (v5_relat_1 @ X0 @ X1)
% 0.20/0.50          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ (sk_B @ X0))
% 0.20/0.50          | (r1_tarski @ (k2_relat_1 @ (sk_B @ X0)) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain, (![X22 : $i]: (v1_relat_1 @ (sk_B @ X22))),
% 0.20/0.50      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.20/0.50  thf('35', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (sk_B @ X0)) @ X0)),
% 0.20/0.50      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.20/0.50          | ((k8_relat_1 @ X9 @ X8) = (X8))
% 0.20/0.50          | ~ (v1_relat_1 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ (sk_B @ X0))
% 0.20/0.50          | ((k8_relat_1 @ X0 @ (sk_B @ X0)) = (sk_B @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, (![X22 : $i]: (v1_relat_1 @ (sk_B @ X22))),
% 0.20/0.50      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X0 : $i]: ((k8_relat_1 @ X0 @ (sk_B @ X0)) = (sk_B @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      ((((k1_xboole_0) = (sk_B @ k1_xboole_0))
% 0.20/0.50        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['30', '39'])).
% 0.20/0.50  thf('41', plain, (![X22 : $i]: (v1_relat_1 @ (sk_B @ X22))),
% 0.20/0.50      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.20/0.50  thf('42', plain, (((k1_xboole_0) = (sk_B @ k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('43', plain, (![X22 : $i]: (v5_ordinal1 @ (sk_B @ X22))),
% 0.20/0.50      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.20/0.50  thf('44', plain, ((v5_ordinal1 @ k1_xboole_0)),
% 0.20/0.50      inference('sup+', [status(thm)], ['42', '43'])).
% 0.20/0.50  thf('45', plain, ($false), inference('demod', [status(thm)], ['29', '44'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
