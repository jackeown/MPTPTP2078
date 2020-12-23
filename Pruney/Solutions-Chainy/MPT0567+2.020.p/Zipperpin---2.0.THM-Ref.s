%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LpQczdu45h

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:44 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 113 expanded)
%              Number of leaves         :   20 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  274 ( 677 expanded)
%              Number of equality atoms :   15 (  35 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k10_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X12 @ X13 ) @ X12 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(t103_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ ( k5_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t103_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('15',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('18',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t171_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k10_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t171_relat_1])).

thf('21',plain,(
    ( k10_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k10_relat_1 @ sk_A @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k10_relat_1 @ sk_A @ X1 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k10_relat_1 @ sk_A @ X1 ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['29','30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LpQczdu45h
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:33:07 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.47/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.47/0.69  % Solved by: fo/fo7.sh
% 0.47/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.69  % done 620 iterations in 0.239s
% 0.47/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.47/0.69  % SZS output start Refutation
% 0.47/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.69  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.47/0.69  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.47/0.69  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.47/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.69  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.47/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.69  thf(d1_xboole_0, axiom,
% 0.47/0.69    (![A:$i]:
% 0.47/0.69     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.47/0.69  thf('0', plain,
% 0.47/0.69      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.47/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.69  thf(t166_relat_1, axiom,
% 0.47/0.69    (![A:$i,B:$i,C:$i]:
% 0.47/0.69     ( ( v1_relat_1 @ C ) =>
% 0.47/0.69       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.47/0.69         ( ?[D:$i]:
% 0.47/0.69           ( ( r2_hidden @ D @ B ) & 
% 0.47/0.69             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.47/0.69             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.47/0.69  thf('1', plain,
% 0.47/0.69      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X13 @ (k10_relat_1 @ X14 @ X12))
% 0.47/0.69          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ X12)
% 0.47/0.69          | ~ (v1_relat_1 @ X14))),
% 0.47/0.69      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.47/0.69  thf('2', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((v1_xboole_0 @ (k10_relat_1 @ X1 @ X0))
% 0.47/0.69          | ~ (v1_relat_1 @ X1)
% 0.47/0.69          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.47/0.69             X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.69  thf(t5_boole, axiom,
% 0.47/0.69    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.47/0.69  thf('3', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.47/0.69      inference('cnf', [status(esa)], [t5_boole])).
% 0.47/0.69  thf(t103_xboole_1, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.47/0.69  thf('4', plain,
% 0.47/0.69      (![X8 : $i, X9 : $i]:
% 0.47/0.69         (r1_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ (k5_xboole_0 @ X8 @ X9))),
% 0.47/0.69      inference('cnf', [status(esa)], [t103_xboole_1])).
% 0.47/0.69  thf('5', plain,
% 0.47/0.69      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 0.47/0.69      inference('sup+', [status(thm)], ['3', '4'])).
% 0.47/0.69  thf('6', plain,
% 0.47/0.69      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.47/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.69  thf(t4_xboole_0, axiom,
% 0.47/0.69    (![A:$i,B:$i]:
% 0.47/0.69     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.69            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.47/0.69       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.47/0.69            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.47/0.69  thf('7', plain,
% 0.47/0.69      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.47/0.69          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.47/0.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.47/0.69  thf('8', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.69  thf('9', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (v1_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['5', '8'])).
% 0.47/0.69  thf(l13_xboole_0, axiom,
% 0.47/0.69    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.69  thf('10', plain,
% 0.47/0.69      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.47/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.69  thf('11', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.69  thf('12', plain,
% 0.47/0.69      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.47/0.69          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.47/0.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.47/0.69  thf('13', plain,
% 0.47/0.69      (![X0 : $i, X1 : $i]:
% 0.47/0.69         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.47/0.69          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 0.47/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.69  thf('14', plain,
% 0.47/0.69      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 0.47/0.69      inference('sup+', [status(thm)], ['3', '4'])).
% 0.47/0.69  thf('15', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.47/0.69      inference('demod', [status(thm)], ['13', '14'])).
% 0.47/0.69  thf('16', plain,
% 0.47/0.69      (![X0 : $i]:
% 0.47/0.69         (~ (v1_relat_1 @ X0)
% 0.47/0.69          | (v1_xboole_0 @ (k10_relat_1 @ X0 @ k1_xboole_0)))),
% 0.47/0.69      inference('sup-', [status(thm)], ['2', '15'])).
% 0.47/0.69  thf('17', plain,
% 0.47/0.69      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.47/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.69  thf('18', plain,
% 0.47/0.69      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.47/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.70  thf('19', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.70      inference('sup+', [status(thm)], ['17', '18'])).
% 0.47/0.70  thf('20', plain,
% 0.47/0.70      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.47/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.47/0.70  thf(t171_relat_1, conjecture,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ A ) =>
% 0.47/0.70       ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.70    (~( ![A:$i]:
% 0.47/0.70        ( ( v1_relat_1 @ A ) =>
% 0.47/0.70          ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) )),
% 0.47/0.70    inference('cnf.neg', [status(esa)], [t171_relat_1])).
% 0.47/0.70  thf('21', plain, (((k10_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('22', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (((k10_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.47/0.70  thf('23', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (((X0) != (k1_xboole_0))
% 0.47/0.70          | ~ (v1_xboole_0 @ X0)
% 0.47/0.70          | ~ (v1_xboole_0 @ (k10_relat_1 @ sk_A @ X1))
% 0.47/0.70          | ~ (v1_xboole_0 @ X1))),
% 0.47/0.70      inference('sup-', [status(thm)], ['19', '22'])).
% 0.47/0.70  thf('24', plain,
% 0.47/0.70      (![X1 : $i]:
% 0.47/0.70         (~ (v1_xboole_0 @ X1)
% 0.47/0.70          | ~ (v1_xboole_0 @ (k10_relat_1 @ sk_A @ X1))
% 0.47/0.70          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['23'])).
% 0.47/0.70  thf('25', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (v1_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['5', '8'])).
% 0.47/0.70  thf('26', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.70  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.70      inference('demod', [status(thm)], ['25', '26'])).
% 0.47/0.70  thf('28', plain,
% 0.47/0.70      (![X1 : $i]:
% 0.47/0.70         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k10_relat_1 @ sk_A @ X1)))),
% 0.47/0.70      inference('demod', [status(thm)], ['24', '27'])).
% 0.47/0.70  thf('29', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['16', '28'])).
% 0.47/0.70  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.70      inference('demod', [status(thm)], ['25', '26'])).
% 0.47/0.70  thf('32', plain, ($false),
% 0.47/0.70      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.47/0.70  
% 0.47/0.70  % SZS output end Refutation
% 0.47/0.70  
% 0.47/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
