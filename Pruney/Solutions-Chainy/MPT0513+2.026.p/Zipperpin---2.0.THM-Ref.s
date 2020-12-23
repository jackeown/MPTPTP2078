%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2mXiNyutdB

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  68 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  296 ( 365 expanded)
%              Number of equality atoms :   42 (  51 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t111_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k7_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t111_relat_1])).

thf('0',plain,(
    ( k7_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t96_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k7_relat_1 @ X39 @ X40 )
        = ( k3_xboole_0 @ X39 @ ( k2_zfmisc_1 @ X40 @ ( k2_relat_1 @ X39 ) ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('3',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k7_relat_1 @ X39 @ X40 )
        = ( k1_setfam_1 @ ( k2_tarski @ X39 @ ( k2_zfmisc_1 @ X40 @ ( k2_relat_1 @ X39 ) ) ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('5',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X4: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','26'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('28',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('29',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('30',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2mXiNyutdB
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:11:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 40 iterations in 0.012s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.44  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.44  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.44  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.44  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.44  thf(t111_relat_1, conjecture,
% 0.20/0.44    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t111_relat_1])).
% 0.20/0.44  thf('0', plain, (((k7_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(t96_relat_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( v1_relat_1 @ B ) =>
% 0.20/0.44       ( ( k7_relat_1 @ B @ A ) =
% 0.20/0.44         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.20/0.44  thf('1', plain,
% 0.20/0.44      (![X39 : $i, X40 : $i]:
% 0.20/0.44         (((k7_relat_1 @ X39 @ X40)
% 0.20/0.44            = (k3_xboole_0 @ X39 @ (k2_zfmisc_1 @ X40 @ (k2_relat_1 @ X39))))
% 0.20/0.44          | ~ (v1_relat_1 @ X39))),
% 0.20/0.44      inference('cnf', [status(esa)], [t96_relat_1])).
% 0.20/0.44  thf(t12_setfam_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.44  thf('2', plain,
% 0.20/0.44      (![X36 : $i, X37 : $i]:
% 0.20/0.44         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.20/0.44      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.44  thf('3', plain,
% 0.20/0.44      (![X39 : $i, X40 : $i]:
% 0.20/0.44         (((k7_relat_1 @ X39 @ X40)
% 0.20/0.44            = (k1_setfam_1 @ 
% 0.20/0.44               (k2_tarski @ X39 @ (k2_zfmisc_1 @ X40 @ (k2_relat_1 @ X39)))))
% 0.20/0.44          | ~ (v1_relat_1 @ X39))),
% 0.20/0.44      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.44  thf(t2_boole, axiom,
% 0.20/0.44    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.44  thf('4', plain,
% 0.20/0.44      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.44      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.44  thf('5', plain,
% 0.20/0.44      (![X36 : $i, X37 : $i]:
% 0.20/0.44         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.20/0.44      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.44  thf('6', plain,
% 0.20/0.44      (![X4 : $i]:
% 0.20/0.44         ((k1_setfam_1 @ (k2_tarski @ X4 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.44      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.44  thf(t100_xboole_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.44  thf('7', plain,
% 0.20/0.44      (![X2 : $i, X3 : $i]:
% 0.20/0.44         ((k4_xboole_0 @ X2 @ X3)
% 0.20/0.44           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.44  thf('8', plain,
% 0.20/0.44      (![X36 : $i, X37 : $i]:
% 0.20/0.44         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.20/0.44      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.44  thf('9', plain,
% 0.20/0.44      (![X2 : $i, X3 : $i]:
% 0.20/0.44         ((k4_xboole_0 @ X2 @ X3)
% 0.20/0.44           = (k5_xboole_0 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X3))))),
% 0.20/0.44      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.44  thf('10', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.44      inference('sup+', [status(thm)], ['6', '9'])).
% 0.20/0.44  thf(t5_boole, axiom,
% 0.20/0.44    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.44  thf('11', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.44      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.44  thf('12', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.44      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.44  thf(t98_xboole_1, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.44  thf('13', plain,
% 0.20/0.44      (![X7 : $i, X8 : $i]:
% 0.20/0.44         ((k2_xboole_0 @ X7 @ X8)
% 0.20/0.44           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.44  thf('14', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.44      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.44  thf(t4_boole, axiom,
% 0.20/0.44    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.44  thf('15', plain,
% 0.20/0.44      (![X5 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.20/0.44      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.44  thf('16', plain,
% 0.20/0.44      (![X7 : $i, X8 : $i]:
% 0.20/0.44         ((k2_xboole_0 @ X7 @ X8)
% 0.20/0.44           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.20/0.44      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.20/0.44  thf('17', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.44      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.44  thf('18', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.44      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.44  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.44      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.44  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.44    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.44  thf('20', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.44      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.44  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.44      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.44  thf('22', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.44      inference('demod', [status(thm)], ['14', '21'])).
% 0.20/0.44  thf('23', plain,
% 0.20/0.44      (![X2 : $i, X3 : $i]:
% 0.20/0.44         ((k4_xboole_0 @ X2 @ X3)
% 0.20/0.44           = (k5_xboole_0 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X3))))),
% 0.20/0.44      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.44  thf('24', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.44           = (k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)))),
% 0.20/0.44      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.44  thf('25', plain,
% 0.20/0.44      (![X5 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.20/0.44      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.44  thf('26', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.20/0.44      inference('sup+', [status(thm)], ['24', '25'])).
% 0.20/0.44  thf('27', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         (((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.20/0.44          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.44      inference('sup+', [status(thm)], ['3', '26'])).
% 0.20/0.44  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.44  thf('28', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.44      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.44  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.44  thf('29', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.20/0.44      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.44  thf('30', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.44      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.44  thf('31', plain,
% 0.20/0.44      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.44      inference('demod', [status(thm)], ['27', '30'])).
% 0.20/0.44  thf('32', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.44      inference('demod', [status(thm)], ['0', '31'])).
% 0.20/0.44  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
