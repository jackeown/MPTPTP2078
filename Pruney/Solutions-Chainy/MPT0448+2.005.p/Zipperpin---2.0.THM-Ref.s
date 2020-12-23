%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MTsiTVRqil

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 (  58 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :  385 ( 454 expanded)
%              Number of equality atoms :   37 (  45 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t32_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_relat_1])).

thf('0',plain,(
    ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t24_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( v1_relat_1 @ E )
     => ( ( E
          = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) )
       => ( ( ( k1_relat_1 @ E )
            = ( k2_tarski @ A @ C ) )
          & ( ( k2_relat_1 @ E )
            = ( k2_tarski @ B @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X35
       != ( k2_tarski @ ( k4_tarski @ X31 @ X32 ) @ ( k4_tarski @ X33 @ X34 ) ) )
      | ( ( k1_relat_1 @ X35 )
        = ( k2_tarski @ X31 @ X33 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t24_relat_1])).

thf('3',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X31 @ X32 ) @ ( k4_tarski @ X33 @ X34 ) ) )
      | ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X31 @ X32 ) @ ( k4_tarski @ X33 @ X34 ) ) )
        = ( k2_tarski @ X31 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(fc7_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) )).

thf('4',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X27 @ X28 ) @ ( k4_tarski @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('5',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X31 @ X32 ) @ ( k4_tarski @ X33 @ X34 ) ) )
      = ( k2_tarski @ X31 @ X33 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k2_tarski @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X26: $i] :
      ( ( ( k3_relat_1 @ X26 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X26 ) @ ( k2_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( X35
       != ( k2_tarski @ ( k4_tarski @ X31 @ X32 ) @ ( k4_tarski @ X33 @ X34 ) ) )
      | ( ( k2_relat_1 @ X35 )
        = ( k2_tarski @ X32 @ X34 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t24_relat_1])).

thf('13',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X31 @ X32 ) @ ( k4_tarski @ X33 @ X34 ) ) )
      | ( ( k2_relat_1 @ ( k2_tarski @ ( k4_tarski @ X31 @ X32 ) @ ( k4_tarski @ X33 @ X34 ) ) )
        = ( k2_tarski @ X32 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X27 @ X28 ) @ ( k4_tarski @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('15',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( k2_relat_1 @ ( k2_tarski @ ( k4_tarski @ X31 @ X32 ) @ ( k4_tarski @ X33 @ X34 ) ) )
      = ( k2_tarski @ X32 @ X34 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('20',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X27 @ X28 ) @ ( k4_tarski @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['10','18','21'])).

thf('23',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X1 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k1_enumset1 @ X4 @ X4 @ X5 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MTsiTVRqil
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:31:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 48 iterations in 0.032s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(t32_relat_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =
% 0.20/0.49       ( k2_tarski @ A @ B ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =
% 0.20/0.49          ( k2_tarski @ A @ B ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t32_relat_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (((k3_relat_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))
% 0.20/0.49         != (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t69_enumset1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.49  thf('1', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf(t24_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ E ) =>
% 0.20/0.49       ( ( ( E ) =
% 0.20/0.49           ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) =>
% 0.20/0.49         ( ( ( k1_relat_1 @ E ) = ( k2_tarski @ A @ C ) ) & 
% 0.20/0.49           ( ( k2_relat_1 @ E ) = ( k2_tarski @ B @ D ) ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.49         (((X35)
% 0.20/0.49            != (k2_tarski @ (k4_tarski @ X31 @ X32) @ (k4_tarski @ X33 @ X34)))
% 0.20/0.49          | ((k1_relat_1 @ X35) = (k2_tarski @ X31 @ X33))
% 0.20/0.49          | ~ (v1_relat_1 @ X35))),
% 0.20/0.49      inference('cnf', [status(esa)], [t24_relat_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ 
% 0.20/0.49             (k2_tarski @ (k4_tarski @ X31 @ X32) @ (k4_tarski @ X33 @ X34)))
% 0.20/0.49          | ((k1_relat_1 @ 
% 0.20/0.49              (k2_tarski @ (k4_tarski @ X31 @ X32) @ (k4_tarski @ X33 @ X34)))
% 0.20/0.49              = (k2_tarski @ X31 @ X33)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.49  thf(fc7_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( v1_relat_1 @
% 0.20/0.49       ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.49         (v1_relat_1 @ 
% 0.20/0.49          (k2_tarski @ (k4_tarski @ X27 @ X28) @ (k4_tarski @ X29 @ X30)))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.49         ((k1_relat_1 @ 
% 0.20/0.49           (k2_tarski @ (k4_tarski @ X31 @ X32) @ (k4_tarski @ X33 @ X34)))
% 0.20/0.49           = (k2_tarski @ X31 @ X33))),
% 0.20/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.20/0.49           = (k2_tarski @ X1 @ X1))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '5'])).
% 0.20/0.49  thf('7', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X1))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf(d6_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( k3_relat_1 @ A ) =
% 0.20/0.49         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X26 : $i]:
% 0.20/0.49         (((k3_relat_1 @ X26)
% 0.20/0.49            = (k2_xboole_0 @ (k1_relat_1 @ X26) @ (k2_relat_1 @ X26)))
% 0.20/0.49          | ~ (v1_relat_1 @ X26))),
% 0.20/0.49      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.20/0.49            = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 0.20/0.49               (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))
% 0.20/0.49          | ~ (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.49         (((X35)
% 0.20/0.49            != (k2_tarski @ (k4_tarski @ X31 @ X32) @ (k4_tarski @ X33 @ X34)))
% 0.20/0.49          | ((k2_relat_1 @ X35) = (k2_tarski @ X32 @ X34))
% 0.20/0.49          | ~ (v1_relat_1 @ X35))),
% 0.20/0.49      inference('cnf', [status(esa)], [t24_relat_1])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ 
% 0.20/0.49             (k2_tarski @ (k4_tarski @ X31 @ X32) @ (k4_tarski @ X33 @ X34)))
% 0.20/0.49          | ((k2_relat_1 @ 
% 0.20/0.49              (k2_tarski @ (k4_tarski @ X31 @ X32) @ (k4_tarski @ X33 @ X34)))
% 0.20/0.49              = (k2_tarski @ X32 @ X34)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.49         (v1_relat_1 @ 
% 0.20/0.49          (k2_tarski @ (k4_tarski @ X27 @ X28) @ (k4_tarski @ X29 @ X30)))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.49         ((k2_relat_1 @ 
% 0.20/0.49           (k2_tarski @ (k4_tarski @ X31 @ X32) @ (k4_tarski @ X33 @ X34)))
% 0.20/0.49           = (k2_tarski @ X32 @ X34))),
% 0.20/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.20/0.49           = (k2_tarski @ X0 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['11', '15'])).
% 0.20/0.49  thf('17', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.49         (v1_relat_1 @ 
% 0.20/0.49          (k2_tarski @ (k4_tarski @ X27 @ X28) @ (k4_tarski @ X29 @ X30)))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.20/0.49           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['10', '18', '21'])).
% 0.20/0.49  thf('23', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf(t43_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.20/0.49       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((k1_enumset1 @ X0 @ X1 @ X2)
% 0.20/0.49           = (k2_xboole_0 @ (k2_tarski @ X0 @ X1) @ (k1_tarski @ X2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.20/0.49           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf(t70_enumset1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]:
% 0.20/0.49         ((k1_enumset1 @ X4 @ X4 @ X5) = (k2_tarski @ X4 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.20/0.49           = (k2_tarski @ X1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.20/0.49           = (k2_tarski @ X1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['22', '27'])).
% 0.20/0.49  thf('29', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '28'])).
% 0.20/0.49  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
