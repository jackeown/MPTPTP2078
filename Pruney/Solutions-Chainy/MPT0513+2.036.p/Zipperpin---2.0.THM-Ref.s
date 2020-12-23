%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yVVFDgzZQt

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:30 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   48 (  66 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  278 ( 417 expanded)
%              Number of equality atoms :   33 (  49 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('0',plain,(
    ! [X45: $i] :
      ( ( v1_relat_1 @ X45 )
      | ( r2_hidden @ ( sk_B @ X45 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X38 @ X39 )
      | ( ( k4_xboole_0 @ X39 @ ( k1_tarski @ X38 ) )
       != X39 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','4'])).

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X53: $i] :
      ( ( ( k7_relat_1 @ X53 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('7',plain,(
    ! [X53: $i] :
      ( ( ( k7_relat_1 @ X53 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf(t101_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ B @ A ) @ A )
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X48 @ X49 ) @ X49 )
        = ( k7_relat_1 @ X48 @ X49 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t101_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
        = ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
        = ( k7_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t61_xboole_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ( r2_xboole_0 @ k1_xboole_0 @ A ) ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X9 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_xboole_1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t102_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('16',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r1_tarski @ X50 @ X51 )
      | ~ ( v1_relat_1 @ X52 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X52 @ X50 ) @ X51 )
        = ( k7_relat_1 @ X52 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t102_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ k1_xboole_0 ) @ X0 )
        = ( k7_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','4'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(condensation,[status(thm)],['20'])).

thf(t111_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k7_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t111_relat_1])).

thf('22',plain,(
    ( k7_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( v1_relat_1 @ X0 ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference('sup-',[status(thm)],['5','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yVVFDgzZQt
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.56  % Solved by: fo/fo7.sh
% 0.35/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.56  % done 211 iterations in 0.097s
% 0.35/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.56  % SZS output start Refutation
% 0.35/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.35/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.56  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.35/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.56  thf(d1_relat_1, axiom,
% 0.35/0.56    (![A:$i]:
% 0.35/0.56     ( ( v1_relat_1 @ A ) <=>
% 0.35/0.56       ( ![B:$i]:
% 0.35/0.56         ( ~( ( r2_hidden @ B @ A ) & 
% 0.35/0.56              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.35/0.56  thf('0', plain,
% 0.35/0.56      (![X45 : $i]: ((v1_relat_1 @ X45) | (r2_hidden @ (sk_B @ X45) @ X45))),
% 0.35/0.56      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.35/0.56  thf(t4_boole, axiom,
% 0.35/0.56    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.56  thf('1', plain,
% 0.35/0.56      (![X8 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.35/0.56      inference('cnf', [status(esa)], [t4_boole])).
% 0.35/0.56  thf(t65_zfmisc_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.35/0.56       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.35/0.56  thf('2', plain,
% 0.35/0.56      (![X38 : $i, X39 : $i]:
% 0.35/0.56         (~ (r2_hidden @ X38 @ X39)
% 0.35/0.56          | ((k4_xboole_0 @ X39 @ (k1_tarski @ X38)) != (X39)))),
% 0.35/0.56      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.35/0.56  thf('3', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.35/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.56  thf('4', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.35/0.56      inference('simplify', [status(thm)], ['3'])).
% 0.35/0.56  thf('5', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.35/0.56      inference('sup-', [status(thm)], ['0', '4'])).
% 0.35/0.56  thf(t110_relat_1, axiom,
% 0.35/0.56    (![A:$i]:
% 0.35/0.56     ( ( v1_relat_1 @ A ) =>
% 0.35/0.56       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.35/0.56  thf('6', plain,
% 0.35/0.56      (![X53 : $i]:
% 0.35/0.56         (((k7_relat_1 @ X53 @ k1_xboole_0) = (k1_xboole_0))
% 0.35/0.56          | ~ (v1_relat_1 @ X53))),
% 0.35/0.56      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.35/0.56  thf('7', plain,
% 0.35/0.56      (![X53 : $i]:
% 0.35/0.56         (((k7_relat_1 @ X53 @ k1_xboole_0) = (k1_xboole_0))
% 0.35/0.56          | ~ (v1_relat_1 @ X53))),
% 0.35/0.56      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.35/0.56  thf(t101_relat_1, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( v1_relat_1 @ B ) =>
% 0.35/0.56       ( ( k7_relat_1 @ ( k7_relat_1 @ B @ A ) @ A ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.35/0.56  thf('8', plain,
% 0.35/0.56      (![X48 : $i, X49 : $i]:
% 0.35/0.56         (((k7_relat_1 @ (k7_relat_1 @ X48 @ X49) @ X49)
% 0.35/0.56            = (k7_relat_1 @ X48 @ X49))
% 0.35/0.56          | ~ (v1_relat_1 @ X48))),
% 0.35/0.56      inference('cnf', [status(esa)], [t101_relat_1])).
% 0.35/0.56  thf('9', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.35/0.56            = (k7_relat_1 @ X0 @ k1_xboole_0))
% 0.35/0.56          | ~ (v1_relat_1 @ X0)
% 0.35/0.56          | ~ (v1_relat_1 @ X0))),
% 0.35/0.56      inference('sup+', [status(thm)], ['7', '8'])).
% 0.35/0.56  thf('10', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (~ (v1_relat_1 @ X0)
% 0.35/0.56          | ((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.35/0.56              = (k7_relat_1 @ X0 @ k1_xboole_0)))),
% 0.35/0.56      inference('simplify', [status(thm)], ['9'])).
% 0.35/0.56  thf('11', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.35/0.56          | ~ (v1_relat_1 @ X0)
% 0.35/0.56          | ~ (v1_relat_1 @ X0))),
% 0.35/0.56      inference('sup+', [status(thm)], ['6', '10'])).
% 0.35/0.56  thf('12', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (~ (v1_relat_1 @ X0)
% 0.35/0.56          | ((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.35/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.35/0.56  thf(t61_xboole_1, axiom,
% 0.35/0.56    (![A:$i]:
% 0.35/0.56     ( ( ( A ) != ( k1_xboole_0 ) ) => ( r2_xboole_0 @ k1_xboole_0 @ A ) ))).
% 0.35/0.56  thf('13', plain,
% 0.35/0.56      (![X9 : $i]: ((r2_xboole_0 @ k1_xboole_0 @ X9) | ((X9) = (k1_xboole_0)))),
% 0.35/0.56      inference('cnf', [status(esa)], [t61_xboole_1])).
% 0.35/0.56  thf(d8_xboole_0, axiom,
% 0.35/0.56    (![A:$i,B:$i]:
% 0.35/0.56     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.35/0.56       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.35/0.56  thf('14', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.35/0.56      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.35/0.56  thf('15', plain,
% 0.35/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.35/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.56  thf(t102_relat_1, axiom,
% 0.35/0.56    (![A:$i,B:$i,C:$i]:
% 0.35/0.56     ( ( v1_relat_1 @ C ) =>
% 0.35/0.56       ( ( r1_tarski @ A @ B ) =>
% 0.35/0.56         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.35/0.56  thf('16', plain,
% 0.35/0.56      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.35/0.56         (~ (r1_tarski @ X50 @ X51)
% 0.35/0.56          | ~ (v1_relat_1 @ X52)
% 0.35/0.56          | ((k7_relat_1 @ (k7_relat_1 @ X52 @ X50) @ X51)
% 0.35/0.56              = (k7_relat_1 @ X52 @ X50)))),
% 0.35/0.56      inference('cnf', [status(esa)], [t102_relat_1])).
% 0.35/0.56  thf('17', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]:
% 0.35/0.56         (((X0) = (k1_xboole_0))
% 0.35/0.56          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ k1_xboole_0) @ X0)
% 0.35/0.56              = (k7_relat_1 @ X1 @ k1_xboole_0))
% 0.35/0.56          | ~ (v1_relat_1 @ X1))),
% 0.35/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.35/0.56  thf('18', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]:
% 0.35/0.56         (((k7_relat_1 @ k1_xboole_0 @ X0)
% 0.35/0.56            = (k7_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.35/0.56          | ~ (v1_relat_1 @ X1)
% 0.35/0.56          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.35/0.56          | ((X0) = (k1_xboole_0)))),
% 0.35/0.56      inference('sup+', [status(thm)], ['12', '17'])).
% 0.35/0.56  thf('19', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.35/0.56      inference('sup-', [status(thm)], ['0', '4'])).
% 0.35/0.56  thf('20', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]:
% 0.35/0.56         (((k7_relat_1 @ k1_xboole_0 @ X0)
% 0.35/0.56            = (k7_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.35/0.56          | ~ (v1_relat_1 @ X1)
% 0.35/0.56          | ((X0) = (k1_xboole_0)))),
% 0.35/0.56      inference('demod', [status(thm)], ['18', '19'])).
% 0.35/0.56  thf('21', plain,
% 0.35/0.56      (![X0 : $i, X1 : $i]:
% 0.35/0.56         (((k7_relat_1 @ k1_xboole_0 @ X0)
% 0.35/0.56            = (k7_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.35/0.56          | ~ (v1_relat_1 @ X1))),
% 0.35/0.56      inference('condensation', [status(thm)], ['20'])).
% 0.35/0.56  thf(t111_relat_1, conjecture,
% 0.35/0.56    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.35/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.56    (~( ![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.35/0.56    inference('cnf.neg', [status(esa)], [t111_relat_1])).
% 0.35/0.56  thf('22', plain, (((k7_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('23', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))
% 0.35/0.56          | ~ (v1_relat_1 @ X0))),
% 0.35/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.56  thf('24', plain,
% 0.35/0.56      (![X0 : $i]:
% 0.35/0.56         (~ (v1_relat_1 @ X0)
% 0.35/0.56          | ((k7_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.35/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.35/0.56  thf('25', plain, (![X0 : $i]: ~ (v1_relat_1 @ X0)),
% 0.35/0.56      inference('clc', [status(thm)], ['23', '24'])).
% 0.35/0.56  thf('26', plain, ($false), inference('sup-', [status(thm)], ['5', '25'])).
% 0.35/0.56  
% 0.35/0.56  % SZS output end Refutation
% 0.35/0.56  
% 0.35/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
