%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ADa1WlmmR3

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  74 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  283 ( 557 expanded)
%              Number of equality atoms :   39 (  73 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t32_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X38 ) )
        = ( k2_tarski @ X37 @ X38 ) )
      | ( X37 = X38 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X33 ) @ X34 )
      | ( r2_hidden @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['9','11'])).

thf('13',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('14',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('19',plain,(
    ! [X39: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['14'])).

thf('22',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('23',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','15','20','21','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ADa1WlmmR3
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 57 iterations in 0.028s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(t32_zfmisc_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.20/0.48       ( k2_tarski @ A @ B ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.20/0.48          ( k2_tarski @ A @ B ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))
% 0.20/0.48         != (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(l51_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X35 : $i, X36 : $i]:
% 0.20/0.48         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.20/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48         != (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(t29_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( A ) != ( B ) ) =>
% 0.20/0.48       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.48         ( k2_tarski @ A @ B ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X37 : $i, X38 : $i]:
% 0.20/0.48         (((k5_xboole_0 @ (k1_tarski @ X37) @ (k1_tarski @ X38))
% 0.20/0.48            = (k2_tarski @ X37 @ X38))
% 0.20/0.48          | ((X37) = (X38)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.20/0.48  thf(l27_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X33 : $i, X34 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ (k1_tarski @ X33) @ X34) | (r2_hidden @ X33 @ X34))),
% 0.20/0.48      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.48  thf(t83_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         (((k4_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r2_hidden @ X1 @ X0)
% 0.20/0.48          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf(t98_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         ((k2_xboole_0 @ X5 @ X6)
% 0.20/0.48           = (k5_xboole_0 @ X5 @ (k4_xboole_0 @ X6 @ X5)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k2_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.20/0.48            = (k5_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.20/0.48          | (r2_hidden @ X0 @ X1))),
% 0.20/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.20/0.48            = (k2_tarski @ X1 @ X0))
% 0.20/0.48          | ((X1) = (X0))
% 0.20/0.48          | (r2_hidden @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['3', '8'])).
% 0.20/0.48  thf(d1_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.48          | ((X10) = (X7))
% 0.20/0.48          | ((X9) != (k1_tarski @ X7)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X7 : $i, X10 : $i]:
% 0.20/0.48         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X1) = (X0))
% 0.20/0.48          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.20/0.48              = (k2_tarski @ X1 @ X0)))),
% 0.20/0.48      inference('clc', [status(thm)], ['9', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.48         != (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 0.20/0.48        | ((sk_A) = (sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain, (((sk_A) = (sk_B))),
% 0.20/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.48  thf(t69_enumset1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X35 : $i, X36 : $i]:
% 0.20/0.48         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.20/0.48      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf(t31_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.20/0.48  thf('19', plain, (![X39 : $i]: ((k3_tarski @ (k1_tarski @ X39)) = (X39))),
% 0.20/0.48      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.20/0.48  thf('20', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain, (((sk_A) = (sk_B))),
% 0.20/0.48      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.48  thf('23', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '15', '20', '21', '22'])).
% 0.20/0.48  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
