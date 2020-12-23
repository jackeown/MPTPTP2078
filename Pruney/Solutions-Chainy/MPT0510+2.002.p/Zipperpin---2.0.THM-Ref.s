%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hjrhj04YOz

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:23 EST 2020

% Result     : Theorem 2.66s
% Output     : Refutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   40 (  53 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :  450 ( 607 expanded)
%              Number of equality atoms :   31 (  44 expanded)
%              Maximal formula depth    :   11 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t96_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ ( k2_zfmisc_1 @ X11 @ ( k2_relat_1 @ X10 ) ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ ( k2_zfmisc_1 @ X11 @ ( k2_relat_1 @ X10 ) ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k3_xboole_0 @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ X1 ) ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ X1 ) ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t116_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t116_xboole_1])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X3 @ X4 ) @ X5 )
      = ( k3_xboole_0 @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ ( k2_relat_1 @ X1 ) ) @ X0 ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k3_xboole_0 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ X1 ) ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ X1 ) ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ ( k2_zfmisc_1 @ X11 @ ( k2_relat_1 @ X10 ) ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf(t122_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ C )
        = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X6 @ X8 ) @ X7 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ ( k2_zfmisc_1 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t122_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ X1 ) ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k7_relat_1 @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k3_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ X2 ) ) )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k3_xboole_0 @ ( k7_relat_1 @ X2 @ X1 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ X2 ) ) )
        = ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k7_relat_1 @ X1 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t108_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t108_relat_1])).

thf('21',plain,(
    ( k7_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( k7_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
     != ( k7_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ( k7_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) )
 != ( k7_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hjrhj04YOz
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.66/2.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.66/2.86  % Solved by: fo/fo7.sh
% 2.66/2.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.66/2.86  % done 623 iterations in 2.409s
% 2.66/2.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.66/2.86  % SZS output start Refutation
% 2.66/2.86  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.66/2.86  thf(sk_C_type, type, sk_C: $i).
% 2.66/2.86  thf(sk_A_type, type, sk_A: $i).
% 2.66/2.86  thf(sk_B_type, type, sk_B: $i).
% 2.66/2.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.66/2.86  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.66/2.86  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.66/2.86  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.66/2.86  thf(t96_relat_1, axiom,
% 2.66/2.86    (![A:$i,B:$i]:
% 2.66/2.86     ( ( v1_relat_1 @ B ) =>
% 2.66/2.86       ( ( k7_relat_1 @ B @ A ) =
% 2.66/2.86         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ))).
% 2.66/2.86  thf('0', plain,
% 2.66/2.86      (![X10 : $i, X11 : $i]:
% 2.66/2.86         (((k7_relat_1 @ X10 @ X11)
% 2.66/2.86            = (k3_xboole_0 @ X10 @ (k2_zfmisc_1 @ X11 @ (k2_relat_1 @ X10))))
% 2.66/2.86          | ~ (v1_relat_1 @ X10))),
% 2.66/2.86      inference('cnf', [status(esa)], [t96_relat_1])).
% 2.66/2.86  thf('1', plain,
% 2.66/2.86      (![X10 : $i, X11 : $i]:
% 2.66/2.86         (((k7_relat_1 @ X10 @ X11)
% 2.66/2.86            = (k3_xboole_0 @ X10 @ (k2_zfmisc_1 @ X11 @ (k2_relat_1 @ X10))))
% 2.66/2.86          | ~ (v1_relat_1 @ X10))),
% 2.66/2.86      inference('cnf', [status(esa)], [t96_relat_1])).
% 2.66/2.86  thf(t16_xboole_1, axiom,
% 2.66/2.86    (![A:$i,B:$i,C:$i]:
% 2.66/2.86     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 2.66/2.86       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.66/2.86  thf('2', plain,
% 2.66/2.86      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.66/2.86         ((k3_xboole_0 @ (k3_xboole_0 @ X3 @ X4) @ X5)
% 2.66/2.86           = (k3_xboole_0 @ X3 @ (k3_xboole_0 @ X4 @ X5)))),
% 2.66/2.86      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.66/2.86  thf('3', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         (((k3_xboole_0 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.66/2.86            = (k3_xboole_0 @ X1 @ 
% 2.66/2.86               (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ X1)) @ X2)))
% 2.66/2.86          | ~ (v1_relat_1 @ X1))),
% 2.66/2.86      inference('sup+', [status(thm)], ['1', '2'])).
% 2.66/2.86  thf('4', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         (((k3_xboole_0 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.66/2.86            = (k3_xboole_0 @ X1 @ 
% 2.66/2.86               (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ X1)) @ X2)))
% 2.66/2.86          | ~ (v1_relat_1 @ X1))),
% 2.66/2.86      inference('sup+', [status(thm)], ['1', '2'])).
% 2.66/2.86  thf(t116_xboole_1, axiom,
% 2.66/2.86    (![A:$i,B:$i,C:$i]:
% 2.66/2.86     ( ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 2.66/2.86       ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 2.66/2.86  thf('5', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 2.66/2.86           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X2)))),
% 2.66/2.86      inference('cnf', [status(esa)], [t116_xboole_1])).
% 2.66/2.86  thf('6', plain,
% 2.66/2.86      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.66/2.86         ((k3_xboole_0 @ (k3_xboole_0 @ X3 @ X4) @ X5)
% 2.66/2.86           = (k3_xboole_0 @ X3 @ (k3_xboole_0 @ X4 @ X5)))),
% 2.66/2.86      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.66/2.86  thf('7', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 2.66/2.86           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X2))))),
% 2.66/2.86      inference('demod', [status(thm)], ['5', '6'])).
% 2.66/2.86  thf('8', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         (((k3_xboole_0 @ X1 @ 
% 2.66/2.86            (k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ (k2_relat_1 @ X1)) @ X0))
% 2.66/2.86            = (k3_xboole_0 @ (k7_relat_1 @ X1 @ X2) @ (k3_xboole_0 @ X1 @ X0)))
% 2.66/2.86          | ~ (v1_relat_1 @ X1))),
% 2.66/2.86      inference('sup+', [status(thm)], ['4', '7'])).
% 2.66/2.86  thf('9', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         (((k3_xboole_0 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 2.66/2.86            = (k3_xboole_0 @ (k7_relat_1 @ X2 @ X1) @ (k3_xboole_0 @ X2 @ X0)))
% 2.66/2.86          | ~ (v1_relat_1 @ X2)
% 2.66/2.86          | ~ (v1_relat_1 @ X2))),
% 2.66/2.86      inference('sup+', [status(thm)], ['3', '8'])).
% 2.66/2.86  thf('10', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         (~ (v1_relat_1 @ X2)
% 2.66/2.86          | ((k3_xboole_0 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 2.66/2.86              = (k3_xboole_0 @ (k7_relat_1 @ X2 @ X1) @ (k3_xboole_0 @ X2 @ X0))))),
% 2.66/2.86      inference('simplify', [status(thm)], ['9'])).
% 2.66/2.86  thf('11', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         (((k3_xboole_0 @ (k7_relat_1 @ X1 @ X2) @ 
% 2.66/2.86            (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ X1)))
% 2.66/2.86            = (k3_xboole_0 @ (k7_relat_1 @ X1 @ X2) @ (k7_relat_1 @ X1 @ X0)))
% 2.66/2.86          | ~ (v1_relat_1 @ X1)
% 2.66/2.86          | ~ (v1_relat_1 @ X1))),
% 2.66/2.86      inference('sup+', [status(thm)], ['0', '10'])).
% 2.66/2.86  thf('12', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         (~ (v1_relat_1 @ X1)
% 2.66/2.86          | ((k3_xboole_0 @ (k7_relat_1 @ X1 @ X2) @ 
% 2.66/2.86              (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ X1)))
% 2.66/2.86              = (k3_xboole_0 @ (k7_relat_1 @ X1 @ X2) @ (k7_relat_1 @ X1 @ X0))))),
% 2.66/2.86      inference('simplify', [status(thm)], ['11'])).
% 2.66/2.86  thf('13', plain,
% 2.66/2.86      (![X10 : $i, X11 : $i]:
% 2.66/2.86         (((k7_relat_1 @ X10 @ X11)
% 2.66/2.86            = (k3_xboole_0 @ X10 @ (k2_zfmisc_1 @ X11 @ (k2_relat_1 @ X10))))
% 2.66/2.86          | ~ (v1_relat_1 @ X10))),
% 2.66/2.86      inference('cnf', [status(esa)], [t96_relat_1])).
% 2.66/2.86  thf(t122_zfmisc_1, axiom,
% 2.66/2.86    (![A:$i,B:$i,C:$i]:
% 2.66/2.86     ( ( ( k2_zfmisc_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 2.66/2.86         ( k3_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 2.66/2.86       ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 2.66/2.86         ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 2.66/2.86  thf('14', plain,
% 2.66/2.86      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.66/2.86         ((k2_zfmisc_1 @ (k3_xboole_0 @ X6 @ X8) @ X7)
% 2.66/2.86           = (k3_xboole_0 @ (k2_zfmisc_1 @ X6 @ X7) @ (k2_zfmisc_1 @ X8 @ X7)))),
% 2.66/2.86      inference('cnf', [status(esa)], [t122_zfmisc_1])).
% 2.66/2.86  thf('15', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         (((k3_xboole_0 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 2.66/2.86            = (k3_xboole_0 @ X1 @ 
% 2.66/2.86               (k3_xboole_0 @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ X1)) @ X2)))
% 2.66/2.86          | ~ (v1_relat_1 @ X1))),
% 2.66/2.86      inference('sup+', [status(thm)], ['1', '2'])).
% 2.66/2.86  thf('16', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         (((k3_xboole_0 @ (k7_relat_1 @ X0 @ X2) @ 
% 2.66/2.86            (k2_zfmisc_1 @ X1 @ (k2_relat_1 @ X0)))
% 2.66/2.86            = (k3_xboole_0 @ X0 @ 
% 2.66/2.86               (k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ (k2_relat_1 @ X0))))
% 2.66/2.86          | ~ (v1_relat_1 @ X0))),
% 2.66/2.86      inference('sup+', [status(thm)], ['14', '15'])).
% 2.66/2.86  thf('17', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         (((k3_xboole_0 @ (k7_relat_1 @ X2 @ X1) @ 
% 2.66/2.86            (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ X2)))
% 2.66/2.86            = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 2.66/2.86          | ~ (v1_relat_1 @ X2)
% 2.66/2.86          | ~ (v1_relat_1 @ X2))),
% 2.66/2.86      inference('sup+', [status(thm)], ['13', '16'])).
% 2.66/2.86  thf('18', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         (~ (v1_relat_1 @ X2)
% 2.66/2.86          | ((k3_xboole_0 @ (k7_relat_1 @ X2 @ X1) @ 
% 2.66/2.86              (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ X2)))
% 2.66/2.86              = (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 2.66/2.86      inference('simplify', [status(thm)], ['17'])).
% 2.66/2.86  thf('19', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         (((k3_xboole_0 @ (k7_relat_1 @ X1 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 2.66/2.86            = (k7_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)))
% 2.66/2.86          | ~ (v1_relat_1 @ X1)
% 2.66/2.86          | ~ (v1_relat_1 @ X1))),
% 2.66/2.86      inference('sup+', [status(thm)], ['12', '18'])).
% 2.66/2.86  thf('20', plain,
% 2.66/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.66/2.86         (~ (v1_relat_1 @ X1)
% 2.66/2.86          | ((k3_xboole_0 @ (k7_relat_1 @ X1 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 2.66/2.86              = (k7_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0))))),
% 2.66/2.86      inference('simplify', [status(thm)], ['19'])).
% 2.66/2.86  thf(t108_relat_1, conjecture,
% 2.66/2.86    (![A:$i,B:$i,C:$i]:
% 2.66/2.86     ( ( v1_relat_1 @ C ) =>
% 2.66/2.86       ( ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 2.66/2.86         ( k3_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 2.66/2.86  thf(zf_stmt_0, negated_conjecture,
% 2.66/2.86    (~( ![A:$i,B:$i,C:$i]:
% 2.66/2.86        ( ( v1_relat_1 @ C ) =>
% 2.66/2.86          ( ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 2.66/2.86            ( k3_xboole_0 @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )),
% 2.66/2.86    inference('cnf.neg', [status(esa)], [t108_relat_1])).
% 2.66/2.86  thf('21', plain,
% 2.66/2.86      (((k7_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B))
% 2.66/2.86         != (k3_xboole_0 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 2.66/2.86             (k7_relat_1 @ sk_C @ sk_B)))),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('22', plain,
% 2.66/2.86      ((((k7_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B))
% 2.66/2.86          != (k7_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)))
% 2.66/2.86        | ~ (v1_relat_1 @ sk_C))),
% 2.66/2.86      inference('sup-', [status(thm)], ['20', '21'])).
% 2.66/2.86  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 2.66/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.66/2.86  thf('24', plain,
% 2.66/2.86      (((k7_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B))
% 2.66/2.86         != (k7_relat_1 @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 2.66/2.86      inference('demod', [status(thm)], ['22', '23'])).
% 2.66/2.86  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 2.66/2.86  
% 2.66/2.86  % SZS output end Refutation
% 2.66/2.86  
% 2.66/2.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
