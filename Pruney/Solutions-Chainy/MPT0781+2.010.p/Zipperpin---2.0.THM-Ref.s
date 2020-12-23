%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pSE2jf81w6

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:31 EST 2020

% Result     : Theorem 0.32s
% Output     : Refutation 0.32s
% Verified   : 
% Statistics : Number of formulae       :   59 (  70 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  379 ( 472 expanded)
%              Number of equality atoms :   30 (  40 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( ( ( k3_relat_1 @ X19 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X19 ) @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ! [X19: $i] :
      ( ( ( k3_relat_1 @ X19 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X19 ) @ ( k2_relat_1 @ X19 ) ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('5',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k3_tarski @ ( k2_tarski @ X7 @ X5 ) ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ ( k2_tarski @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( ( k8_relat_1 @ X21 @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 )
        = X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X19: $i] :
      ( ( ( k3_relat_1 @ X19 )
        = ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X19 ) @ ( k2_relat_1 @ X19 ) ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X17 @ X18 ) )
      = ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k3_tarski @ ( k2_tarski @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( ( k7_relat_1 @ X22 @ X23 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ ( k3_tarski @ ( k2_tarski @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t18_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_wellord1 @ X25 @ X24 )
        = ( k8_relat_1 @ X24 @ ( k7_relat_1 @ X25 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t18_wellord1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ X0 @ ( k3_relat_1 @ X0 ) )
        = ( k8_relat_1 @ ( k3_relat_1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t30_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t30_wellord1])).

thf('27',plain,(
    ( k2_wellord1 @ sk_A @ ( k3_relat_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k8_relat_1 @ ( k3_relat_1 @ sk_A ) @ sk_A )
     != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ( k8_relat_1 @ ( k3_relat_1 @ sk_A ) @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pSE2jf81w6
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:53:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.32/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.32/0.52  % Solved by: fo/fo7.sh
% 0.32/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.32/0.52  % done 70 iterations in 0.057s
% 0.32/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.32/0.52  % SZS output start Refutation
% 0.32/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.32/0.52  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.32/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.32/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.32/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.32/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.32/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.32/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.32/0.52  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.32/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.32/0.52  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.32/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.32/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.32/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.32/0.52  thf(d6_relat_1, axiom,
% 0.32/0.52    (![A:$i]:
% 0.32/0.52     ( ( v1_relat_1 @ A ) =>
% 0.32/0.52       ( ( k3_relat_1 @ A ) =
% 0.32/0.52         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.32/0.52  thf('0', plain,
% 0.32/0.52      (![X19 : $i]:
% 0.32/0.52         (((k3_relat_1 @ X19)
% 0.32/0.52            = (k2_xboole_0 @ (k1_relat_1 @ X19) @ (k2_relat_1 @ X19)))
% 0.32/0.52          | ~ (v1_relat_1 @ X19))),
% 0.32/0.52      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.32/0.52  thf(l51_zfmisc_1, axiom,
% 0.32/0.52    (![A:$i,B:$i]:
% 0.32/0.52     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.32/0.52  thf('1', plain,
% 0.32/0.52      (![X17 : $i, X18 : $i]:
% 0.32/0.52         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.32/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.32/0.52  thf('2', plain,
% 0.32/0.52      (![X19 : $i]:
% 0.32/0.52         (((k3_relat_1 @ X19)
% 0.32/0.52            = (k3_tarski @ 
% 0.32/0.52               (k2_tarski @ (k1_relat_1 @ X19) @ (k2_relat_1 @ X19))))
% 0.32/0.52          | ~ (v1_relat_1 @ X19))),
% 0.32/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.32/0.52  thf(d3_tarski, axiom,
% 0.32/0.52    (![A:$i,B:$i]:
% 0.32/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.32/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.32/0.52  thf('3', plain,
% 0.32/0.52      (![X1 : $i, X3 : $i]:
% 0.32/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.32/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.32/0.52  thf(d3_xboole_0, axiom,
% 0.32/0.52    (![A:$i,B:$i,C:$i]:
% 0.32/0.52     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.32/0.52       ( ![D:$i]:
% 0.32/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.32/0.52           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.32/0.52  thf('4', plain,
% 0.32/0.52      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.32/0.52         (~ (r2_hidden @ X4 @ X5)
% 0.32/0.52          | (r2_hidden @ X4 @ X6)
% 0.32/0.52          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.32/0.52      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.32/0.52  thf('5', plain,
% 0.32/0.52      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.32/0.52         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.32/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.32/0.52  thf('6', plain,
% 0.32/0.52      (![X17 : $i, X18 : $i]:
% 0.32/0.52         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.32/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.32/0.52  thf('7', plain,
% 0.32/0.52      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.32/0.52         ((r2_hidden @ X4 @ (k3_tarski @ (k2_tarski @ X7 @ X5)))
% 0.32/0.52          | ~ (r2_hidden @ X4 @ X5))),
% 0.32/0.52      inference('demod', [status(thm)], ['5', '6'])).
% 0.32/0.52  thf('8', plain,
% 0.32/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.32/0.52         ((r1_tarski @ X0 @ X1)
% 0.32/0.52          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ (k2_tarski @ X2 @ X0))))),
% 0.32/0.52      inference('sup-', [status(thm)], ['3', '7'])).
% 0.32/0.52  thf('9', plain,
% 0.32/0.52      (![X1 : $i, X3 : $i]:
% 0.32/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.32/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.32/0.52  thf('10', plain,
% 0.32/0.52      (![X0 : $i, X1 : $i]:
% 0.32/0.52         ((r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))
% 0.32/0.52          | (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 0.32/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.32/0.52  thf('11', plain,
% 0.32/0.52      (![X0 : $i, X1 : $i]:
% 0.32/0.52         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.32/0.52      inference('simplify', [status(thm)], ['10'])).
% 0.32/0.52  thf('12', plain,
% 0.32/0.52      (![X0 : $i]:
% 0.32/0.52         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.32/0.52          | ~ (v1_relat_1 @ X0))),
% 0.32/0.52      inference('sup+', [status(thm)], ['2', '11'])).
% 0.32/0.52  thf(t125_relat_1, axiom,
% 0.32/0.52    (![A:$i,B:$i]:
% 0.32/0.52     ( ( v1_relat_1 @ B ) =>
% 0.32/0.52       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.32/0.52         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.32/0.52  thf('13', plain,
% 0.32/0.52      (![X20 : $i, X21 : $i]:
% 0.32/0.52         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.32/0.52          | ((k8_relat_1 @ X21 @ X20) = (X20))
% 0.32/0.52          | ~ (v1_relat_1 @ X20))),
% 0.32/0.52      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.32/0.52  thf('14', plain,
% 0.32/0.52      (![X0 : $i]:
% 0.32/0.52         (~ (v1_relat_1 @ X0)
% 0.32/0.52          | ~ (v1_relat_1 @ X0)
% 0.32/0.52          | ((k8_relat_1 @ (k3_relat_1 @ X0) @ X0) = (X0)))),
% 0.32/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.32/0.52  thf('15', plain,
% 0.32/0.52      (![X0 : $i]:
% 0.32/0.52         (((k8_relat_1 @ (k3_relat_1 @ X0) @ X0) = (X0)) | ~ (v1_relat_1 @ X0))),
% 0.32/0.52      inference('simplify', [status(thm)], ['14'])).
% 0.32/0.52  thf('16', plain,
% 0.32/0.52      (![X19 : $i]:
% 0.32/0.52         (((k3_relat_1 @ X19)
% 0.32/0.52            = (k3_tarski @ 
% 0.32/0.52               (k2_tarski @ (k1_relat_1 @ X19) @ (k2_relat_1 @ X19))))
% 0.32/0.52          | ~ (v1_relat_1 @ X19))),
% 0.32/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.32/0.52  thf(t7_xboole_1, axiom,
% 0.32/0.52    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.32/0.52  thf('17', plain,
% 0.32/0.52      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.32/0.52      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.32/0.52  thf('18', plain,
% 0.32/0.52      (![X17 : $i, X18 : $i]:
% 0.32/0.52         ((k3_tarski @ (k2_tarski @ X17 @ X18)) = (k2_xboole_0 @ X17 @ X18))),
% 0.32/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.32/0.52  thf('19', plain,
% 0.32/0.52      (![X10 : $i, X11 : $i]:
% 0.32/0.52         (r1_tarski @ X10 @ (k3_tarski @ (k2_tarski @ X10 @ X11)))),
% 0.32/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.32/0.52  thf(t97_relat_1, axiom,
% 0.32/0.52    (![A:$i,B:$i]:
% 0.32/0.52     ( ( v1_relat_1 @ B ) =>
% 0.32/0.52       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.32/0.52         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.32/0.52  thf('20', plain,
% 0.32/0.52      (![X22 : $i, X23 : $i]:
% 0.32/0.52         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 0.32/0.52          | ((k7_relat_1 @ X22 @ X23) = (X22))
% 0.32/0.52          | ~ (v1_relat_1 @ X22))),
% 0.32/0.52      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.32/0.52  thf('21', plain,
% 0.32/0.52      (![X0 : $i, X1 : $i]:
% 0.32/0.52         (~ (v1_relat_1 @ X1)
% 0.32/0.52          | ((k7_relat_1 @ X1 @ 
% 0.32/0.52              (k3_tarski @ (k2_tarski @ (k1_relat_1 @ X1) @ X0))) = (X1)))),
% 0.32/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.32/0.52  thf('22', plain,
% 0.32/0.52      (![X0 : $i]:
% 0.32/0.52         (((k7_relat_1 @ X0 @ (k3_relat_1 @ X0)) = (X0))
% 0.32/0.52          | ~ (v1_relat_1 @ X0)
% 0.32/0.52          | ~ (v1_relat_1 @ X0))),
% 0.32/0.52      inference('sup+', [status(thm)], ['16', '21'])).
% 0.32/0.52  thf('23', plain,
% 0.32/0.52      (![X0 : $i]:
% 0.32/0.52         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k3_relat_1 @ X0)) = (X0)))),
% 0.32/0.52      inference('simplify', [status(thm)], ['22'])).
% 0.32/0.52  thf(t18_wellord1, axiom,
% 0.32/0.52    (![A:$i,B:$i]:
% 0.32/0.52     ( ( v1_relat_1 @ B ) =>
% 0.32/0.52       ( ( k2_wellord1 @ B @ A ) = ( k8_relat_1 @ A @ ( k7_relat_1 @ B @ A ) ) ) ))).
% 0.32/0.52  thf('24', plain,
% 0.32/0.52      (![X24 : $i, X25 : $i]:
% 0.32/0.52         (((k2_wellord1 @ X25 @ X24)
% 0.32/0.52            = (k8_relat_1 @ X24 @ (k7_relat_1 @ X25 @ X24)))
% 0.32/0.52          | ~ (v1_relat_1 @ X25))),
% 0.32/0.52      inference('cnf', [status(esa)], [t18_wellord1])).
% 0.32/0.52  thf('25', plain,
% 0.32/0.52      (![X0 : $i]:
% 0.32/0.52         (((k2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.32/0.52            = (k8_relat_1 @ (k3_relat_1 @ X0) @ X0))
% 0.32/0.52          | ~ (v1_relat_1 @ X0)
% 0.32/0.52          | ~ (v1_relat_1 @ X0))),
% 0.32/0.52      inference('sup+', [status(thm)], ['23', '24'])).
% 0.32/0.52  thf('26', plain,
% 0.32/0.52      (![X0 : $i]:
% 0.32/0.52         (~ (v1_relat_1 @ X0)
% 0.32/0.52          | ((k2_wellord1 @ X0 @ (k3_relat_1 @ X0))
% 0.32/0.52              = (k8_relat_1 @ (k3_relat_1 @ X0) @ X0)))),
% 0.32/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.32/0.52  thf(t30_wellord1, conjecture,
% 0.32/0.52    (![A:$i]:
% 0.32/0.52     ( ( v1_relat_1 @ A ) =>
% 0.32/0.52       ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ))).
% 0.32/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.32/0.52    (~( ![A:$i]:
% 0.32/0.52        ( ( v1_relat_1 @ A ) =>
% 0.32/0.52          ( ( k2_wellord1 @ A @ ( k3_relat_1 @ A ) ) = ( A ) ) ) )),
% 0.32/0.52    inference('cnf.neg', [status(esa)], [t30_wellord1])).
% 0.32/0.52  thf('27', plain, (((k2_wellord1 @ sk_A @ (k3_relat_1 @ sk_A)) != (sk_A))),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('28', plain,
% 0.32/0.52      ((((k8_relat_1 @ (k3_relat_1 @ sk_A) @ sk_A) != (sk_A))
% 0.32/0.52        | ~ (v1_relat_1 @ sk_A))),
% 0.32/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.32/0.52  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('30', plain, (((k8_relat_1 @ (k3_relat_1 @ sk_A) @ sk_A) != (sk_A))),
% 0.32/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.32/0.52  thf('31', plain, ((((sk_A) != (sk_A)) | ~ (v1_relat_1 @ sk_A))),
% 0.32/0.52      inference('sup-', [status(thm)], ['15', '30'])).
% 0.32/0.52  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 0.32/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.32/0.52  thf('33', plain, (((sk_A) != (sk_A))),
% 0.32/0.52      inference('demod', [status(thm)], ['31', '32'])).
% 0.32/0.52  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.32/0.52  
% 0.32/0.52  % SZS output end Refutation
% 0.32/0.52  
% 0.32/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
