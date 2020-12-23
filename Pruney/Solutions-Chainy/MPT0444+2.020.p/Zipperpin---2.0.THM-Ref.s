%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vhP4jzq5pR

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  72 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  374 ( 580 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k4_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( r1_tarski @ ( k2_relat_1 @ X30 ) @ ( k2_relat_1 @ X29 ) )
      | ~ ( r1_tarski @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( v1_relat_1 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['8','13'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( r1_tarski @ ( k2_relat_1 @ X30 ) @ ( k2_relat_1 @ X29 ) )
      | ~ ( r1_tarski @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('19',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( v1_relat_1 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['17','22'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf(t27_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_relat_1])).

thf('27',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['28','29','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vhP4jzq5pR
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:44:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.59  % Solved by: fo/fo7.sh
% 0.21/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.59  % done 281 iterations in 0.139s
% 0.21/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.59  % SZS output start Refutation
% 0.21/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.59  thf(t51_xboole_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.21/0.59       ( A ) ))).
% 0.21/0.59  thf('0', plain,
% 0.21/0.59      (![X13 : $i, X14 : $i]:
% 0.21/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 0.21/0.59           = (X13))),
% 0.21/0.59      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.21/0.59  thf(t31_xboole_1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( r1_tarski @
% 0.21/0.59       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.21/0.59       ( k2_xboole_0 @ B @ C ) ))).
% 0.21/0.59  thf('1', plain,
% 0.21/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.59         (r1_tarski @ 
% 0.21/0.59          (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k3_xboole_0 @ X10 @ X12)) @ 
% 0.21/0.59          (k2_xboole_0 @ X11 @ X12))),
% 0.21/0.59      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.21/0.59  thf(t23_xboole_1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.21/0.59       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.21/0.59  thf('2', plain,
% 0.21/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.59         ((k3_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.21/0.59           = (k2_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X9)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t23_xboole_1])).
% 0.21/0.59  thf('3', plain,
% 0.21/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.59         (r1_tarski @ (k3_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)) @ 
% 0.21/0.59          (k2_xboole_0 @ X11 @ X12))),
% 0.21/0.59      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.59  thf('4', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ 
% 0.21/0.59          (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.59      inference('sup+', [status(thm)], ['0', '3'])).
% 0.21/0.59  thf('5', plain,
% 0.21/0.59      (![X13 : $i, X14 : $i]:
% 0.21/0.59         ((k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ (k4_xboole_0 @ X13 @ X14))
% 0.21/0.59           = (X13))),
% 0.21/0.59      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.21/0.59  thf('6', plain,
% 0.21/0.59      (![X0 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ X0)),
% 0.21/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.59  thf(t25_relat_1, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ A ) =>
% 0.21/0.59       ( ![B:$i]:
% 0.21/0.59         ( ( v1_relat_1 @ B ) =>
% 0.21/0.59           ( ( r1_tarski @ A @ B ) =>
% 0.21/0.59             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.59               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.59  thf('7', plain,
% 0.21/0.59      (![X29 : $i, X30 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X29)
% 0.21/0.59          | (r1_tarski @ (k2_relat_1 @ X30) @ (k2_relat_1 @ X29))
% 0.21/0.59          | ~ (r1_tarski @ X30 @ X29)
% 0.21/0.59          | ~ (v1_relat_1 @ X30))),
% 0.21/0.59      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.21/0.59  thf('8', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.59          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.21/0.59             (k2_relat_1 @ X0))
% 0.21/0.59          | ~ (v1_relat_1 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.59  thf('9', plain,
% 0.21/0.59      (![X0 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X0) @ X0)),
% 0.21/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.59  thf(t3_subset, axiom,
% 0.21/0.59    (![A:$i,B:$i]:
% 0.21/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.59  thf('10', plain,
% 0.21/0.59      (![X24 : $i, X26 : $i]:
% 0.21/0.59         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 0.21/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.59  thf('11', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.59  thf(cc2_relat_1, axiom,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ A ) =>
% 0.21/0.59       ( ![B:$i]:
% 0.21/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.59  thf('12', plain,
% 0.21/0.59      (![X27 : $i, X28 : $i]:
% 0.21/0.59         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.21/0.59          | (v1_relat_1 @ X27)
% 0.21/0.59          | ~ (v1_relat_1 @ X28))),
% 0.21/0.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.59  thf('13', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.59  thf('14', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X0)
% 0.21/0.59          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.21/0.59             (k2_relat_1 @ X0)))),
% 0.21/0.59      inference('clc', [status(thm)], ['8', '13'])).
% 0.21/0.59  thf(t17_xboole_1, axiom,
% 0.21/0.59    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.59  thf('15', plain,
% 0.21/0.59      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.21/0.59      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.59  thf('16', plain,
% 0.21/0.59      (![X29 : $i, X30 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X29)
% 0.21/0.59          | (r1_tarski @ (k2_relat_1 @ X30) @ (k2_relat_1 @ X29))
% 0.21/0.59          | ~ (r1_tarski @ X30 @ X29)
% 0.21/0.59          | ~ (v1_relat_1 @ X30))),
% 0.21/0.59      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.21/0.59  thf('17', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.21/0.59          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.21/0.59             (k2_relat_1 @ X0))
% 0.21/0.59          | ~ (v1_relat_1 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.59  thf('18', plain,
% 0.21/0.59      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.21/0.59      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.59  thf('19', plain,
% 0.21/0.59      (![X24 : $i, X26 : $i]:
% 0.21/0.59         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 0.21/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.59  thf('20', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.59  thf('21', plain,
% 0.21/0.59      (![X27 : $i, X28 : $i]:
% 0.21/0.59         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.21/0.59          | (v1_relat_1 @ X27)
% 0.21/0.59          | ~ (v1_relat_1 @ X28))),
% 0.21/0.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.59  thf('22', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.59  thf('23', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X0)
% 0.21/0.59          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.21/0.59             (k2_relat_1 @ X0)))),
% 0.21/0.59      inference('clc', [status(thm)], ['17', '22'])).
% 0.21/0.59  thf(t19_xboole_1, axiom,
% 0.21/0.59    (![A:$i,B:$i,C:$i]:
% 0.21/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.21/0.59       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.59  thf('24', plain,
% 0.21/0.59      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.59         (~ (r1_tarski @ X4 @ X5)
% 0.21/0.59          | ~ (r1_tarski @ X4 @ X6)
% 0.21/0.59          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.21/0.59      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.21/0.59  thf('25', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X0)
% 0.21/0.59          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.21/0.59             (k3_xboole_0 @ (k2_relat_1 @ X0) @ X2))
% 0.21/0.59          | ~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 0.21/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.59  thf('26', plain,
% 0.21/0.59      (![X0 : $i, X1 : $i]:
% 0.21/0.59         (~ (v1_relat_1 @ X0)
% 0.21/0.59          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.21/0.59             (k3_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 0.21/0.59          | ~ (v1_relat_1 @ X1))),
% 0.21/0.59      inference('sup-', [status(thm)], ['14', '25'])).
% 0.21/0.59  thf(t27_relat_1, conjecture,
% 0.21/0.59    (![A:$i]:
% 0.21/0.59     ( ( v1_relat_1 @ A ) =>
% 0.21/0.59       ( ![B:$i]:
% 0.21/0.59         ( ( v1_relat_1 @ B ) =>
% 0.21/0.59           ( r1_tarski @
% 0.21/0.59             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.21/0.59             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.59    (~( ![A:$i]:
% 0.21/0.59        ( ( v1_relat_1 @ A ) =>
% 0.21/0.59          ( ![B:$i]:
% 0.21/0.59            ( ( v1_relat_1 @ B ) =>
% 0.21/0.59              ( r1_tarski @
% 0.21/0.59                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.21/0.59                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 0.21/0.59    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 0.21/0.59  thf('27', plain,
% 0.21/0.59      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.21/0.59          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('28', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.59  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.59  thf('31', plain, ($false),
% 0.21/0.59      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.59  
% 0.21/0.59  % SZS output end Refutation
% 0.21/0.59  
% 0.43/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
