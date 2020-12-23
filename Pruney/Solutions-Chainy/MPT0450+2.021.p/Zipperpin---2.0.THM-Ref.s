%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vHojliePvs

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:04 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   51 (  70 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  361 ( 550 expanded)
%              Number of equality atoms :    6 (  14 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( r1_tarski @ ( k3_relat_1 @ X32 ) @ ( k3_relat_1 @ X31 ) )
      | ~ ( r1_tarski @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( v1_relat_1 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['8','13'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('16',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( r1_tarski @ ( k3_relat_1 @ X32 ) @ ( k3_relat_1 @ X31 ) )
      | ~ ( r1_tarski @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('19',plain,(
    ! [X26: $i,X28: $i] :
      ( ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( r1_tarski @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( v1_relat_1 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['17','22'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','25'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('27',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vHojliePvs
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.70  % Solved by: fo/fo7.sh
% 0.51/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.70  % done 374 iterations in 0.246s
% 0.51/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.70  % SZS output start Refutation
% 0.51/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.70  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.51/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.70  thf(t16_xboole_1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.51/0.70       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.51/0.70  thf('0', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.70         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2)
% 0.51/0.70           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.51/0.70      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.51/0.70  thf(t22_xboole_1, axiom,
% 0.51/0.70    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.51/0.70  thf('1', plain,
% 0.51/0.70      (![X8 : $i, X9 : $i]:
% 0.51/0.70         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 0.51/0.70      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.51/0.70  thf('2', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.70         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ 
% 0.51/0.70           (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.51/0.70           = (k3_xboole_0 @ X2 @ X1))),
% 0.51/0.70      inference('sup+', [status(thm)], ['0', '1'])).
% 0.51/0.70  thf(t31_xboole_1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( r1_tarski @
% 0.51/0.70       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 0.51/0.70       ( k2_xboole_0 @ B @ C ) ))).
% 0.51/0.70  thf('3', plain,
% 0.51/0.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.51/0.70         (r1_tarski @ 
% 0.51/0.70          (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k3_xboole_0 @ X10 @ X12)) @ 
% 0.51/0.70          (k2_xboole_0 @ X11 @ X12))),
% 0.51/0.70      inference('cnf', [status(esa)], [t31_xboole_1])).
% 0.51/0.70  thf('4', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.70         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ 
% 0.51/0.70          (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X2)))),
% 0.51/0.70      inference('sup+', [status(thm)], ['2', '3'])).
% 0.51/0.70  thf('5', plain,
% 0.51/0.70      (![X8 : $i, X9 : $i]:
% 0.51/0.70         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 0.51/0.70      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.51/0.70  thf('6', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.51/0.70      inference('demod', [status(thm)], ['4', '5'])).
% 0.51/0.70  thf(t31_relat_1, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( v1_relat_1 @ A ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( v1_relat_1 @ B ) =>
% 0.51/0.70           ( ( r1_tarski @ A @ B ) =>
% 0.51/0.70             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.51/0.70  thf('7', plain,
% 0.51/0.70      (![X31 : $i, X32 : $i]:
% 0.51/0.70         (~ (v1_relat_1 @ X31)
% 0.51/0.70          | (r1_tarski @ (k3_relat_1 @ X32) @ (k3_relat_1 @ X31))
% 0.51/0.70          | ~ (r1_tarski @ X32 @ X31)
% 0.51/0.70          | ~ (v1_relat_1 @ X32))),
% 0.51/0.70      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.51/0.70  thf('8', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.51/0.70          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.51/0.70             (k3_relat_1 @ X0))
% 0.51/0.70          | ~ (v1_relat_1 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.51/0.70  thf('9', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.51/0.70      inference('demod', [status(thm)], ['4', '5'])).
% 0.51/0.70  thf(t3_subset, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.51/0.70  thf('10', plain,
% 0.51/0.70      (![X26 : $i, X28 : $i]:
% 0.51/0.70         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 0.51/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.70  thf('11', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.70  thf(cc2_relat_1, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( v1_relat_1 @ A ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.51/0.70  thf('12', plain,
% 0.51/0.70      (![X29 : $i, X30 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.51/0.70          | (v1_relat_1 @ X29)
% 0.51/0.70          | ~ (v1_relat_1 @ X30))),
% 0.51/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.51/0.70  thf('13', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.51/0.70  thf('14', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (v1_relat_1 @ X0)
% 0.51/0.70          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.51/0.70             (k3_relat_1 @ X0)))),
% 0.51/0.70      inference('clc', [status(thm)], ['8', '13'])).
% 0.51/0.70  thf(t17_xboole_1, axiom,
% 0.51/0.70    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.51/0.70  thf('15', plain,
% 0.51/0.70      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.51/0.70      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.51/0.70  thf('16', plain,
% 0.51/0.70      (![X31 : $i, X32 : $i]:
% 0.51/0.70         (~ (v1_relat_1 @ X31)
% 0.51/0.70          | (r1_tarski @ (k3_relat_1 @ X32) @ (k3_relat_1 @ X31))
% 0.51/0.70          | ~ (r1_tarski @ X32 @ X31)
% 0.51/0.70          | ~ (v1_relat_1 @ X32))),
% 0.51/0.70      inference('cnf', [status(esa)], [t31_relat_1])).
% 0.51/0.70  thf('17', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 0.51/0.70          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.51/0.70             (k3_relat_1 @ X0))
% 0.51/0.70          | ~ (v1_relat_1 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['15', '16'])).
% 0.51/0.70  thf('18', plain,
% 0.51/0.70      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.51/0.70      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.51/0.70  thf('19', plain,
% 0.51/0.70      (![X26 : $i, X28 : $i]:
% 0.51/0.70         ((m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X28)) | ~ (r1_tarski @ X26 @ X28))),
% 0.51/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.70  thf('20', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.51/0.70  thf('21', plain,
% 0.51/0.70      (![X29 : $i, X30 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.51/0.70          | (v1_relat_1 @ X29)
% 0.51/0.70          | ~ (v1_relat_1 @ X30))),
% 0.51/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.51/0.70  thf('22', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.51/0.70  thf('23', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (v1_relat_1 @ X0)
% 0.51/0.70          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.51/0.70             (k3_relat_1 @ X0)))),
% 0.51/0.70      inference('clc', [status(thm)], ['17', '22'])).
% 0.51/0.70  thf(t19_xboole_1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.51/0.70       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.51/0.70  thf('24', plain,
% 0.51/0.70      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.51/0.70         (~ (r1_tarski @ X5 @ X6)
% 0.51/0.70          | ~ (r1_tarski @ X5 @ X7)
% 0.51/0.70          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.51/0.70      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.51/0.70  thf('25', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.70         (~ (v1_relat_1 @ X0)
% 0.51/0.70          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.51/0.70             (k3_xboole_0 @ (k3_relat_1 @ X0) @ X2))
% 0.51/0.70          | ~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 0.51/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.51/0.70  thf('26', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (v1_relat_1 @ X0)
% 0.51/0.70          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.51/0.70             (k3_xboole_0 @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0)))
% 0.51/0.70          | ~ (v1_relat_1 @ X1))),
% 0.51/0.70      inference('sup-', [status(thm)], ['14', '25'])).
% 0.51/0.70  thf(t34_relat_1, conjecture,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( v1_relat_1 @ A ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( v1_relat_1 @ B ) =>
% 0.51/0.70           ( r1_tarski @
% 0.51/0.70             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.51/0.70             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 0.51/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.70    (~( ![A:$i]:
% 0.51/0.70        ( ( v1_relat_1 @ A ) =>
% 0.51/0.70          ( ![B:$i]:
% 0.51/0.70            ( ( v1_relat_1 @ B ) =>
% 0.51/0.70              ( r1_tarski @
% 0.51/0.70                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.51/0.70                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 0.51/0.70    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 0.51/0.70  thf('27', plain,
% 0.51/0.70      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.51/0.70          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('28', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.51/0.70      inference('sup-', [status(thm)], ['26', '27'])).
% 0.51/0.70  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('31', plain, ($false),
% 0.51/0.70      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.51/0.70  
% 0.51/0.70  % SZS output end Refutation
% 0.51/0.70  
% 0.51/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
