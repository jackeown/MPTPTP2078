%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pcaaNLcAuo

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:53 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   57 (  66 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  408 ( 511 expanded)
%              Number of equality atoms :   47 (  63 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('2',plain,(
    r1_tarski @ ( k1_enumset1 @ sk_A @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('4',plain,(
    ! [X55: $i,X57: $i,X58: $i] :
      ( ( r1_tarski @ X57 @ ( k2_tarski @ X55 @ X58 ) )
      | ( X57
       != ( k1_tarski @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('5',plain,(
    ! [X55: $i,X58: $i] :
      ( r1_tarski @ ( k1_tarski @ X55 ) @ ( k2_tarski @ X55 @ X58 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('12',plain,(
    ! [X51: $i,X53: $i,X54: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X51 @ X53 ) @ X54 )
        = ( k1_tarski @ X51 ) )
      | ( X51 != X53 )
      | ( r2_hidden @ X51 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('13',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r2_hidden @ X53 @ X54 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X53 @ X53 ) @ X54 )
        = ( k1_tarski @ X53 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r2_hidden @ X53 @ X54 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X53 ) @ X54 )
        = ( k1_tarski @ X53 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( r2_hidden @ X51 @ X52 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X51 @ X53 ) @ X52 )
       != ( k1_tarski @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
       != ( k1_tarski @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X18 != X17 )
      | ( r2_hidden @ X18 @ X19 )
      | ( X19
       != ( k2_tarski @ X20 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('24',plain,(
    ! [X17: $i,X20: $i] :
      ( r2_hidden @ X17 @ ( k2_tarski @ X20 @ X17 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','25'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['11','26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X17: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X19 )
      | ( X21 = X20 )
      | ( X21 = X17 )
      | ( X19
       != ( k2_tarski @ X20 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('30',plain,(
    ! [X17: $i,X20: $i,X21: $i] :
      ( ( X21 = X17 )
      | ( X21 = X20 )
      | ~ ( r2_hidden @ X21 @ ( k2_tarski @ X20 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pcaaNLcAuo
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.66  % Solved by: fo/fo7.sh
% 0.44/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.66  % done 460 iterations in 0.200s
% 0.44/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.66  % SZS output start Refutation
% 0.44/0.66  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.44/0.66  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.44/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.66  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.44/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.44/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.66  thf(t28_zfmisc_1, conjecture,
% 0.44/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.66     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.44/0.66          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.44/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.66    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.66        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.44/0.66             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.44/0.66    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.44/0.66  thf('0', plain,
% 0.44/0.66      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(t70_enumset1, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.44/0.66  thf('1', plain,
% 0.44/0.66      (![X24 : $i, X25 : $i]:
% 0.44/0.66         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.44/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.44/0.66  thf('2', plain,
% 0.44/0.66      ((r1_tarski @ (k1_enumset1 @ sk_A @ sk_A @ sk_B_1) @ 
% 0.44/0.66        (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.44/0.66      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.66  thf('3', plain,
% 0.44/0.66      (![X24 : $i, X25 : $i]:
% 0.44/0.66         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.44/0.66      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.44/0.66  thf(l45_zfmisc_1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.44/0.66       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.44/0.66            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.44/0.66  thf('4', plain,
% 0.44/0.66      (![X55 : $i, X57 : $i, X58 : $i]:
% 0.44/0.66         ((r1_tarski @ X57 @ (k2_tarski @ X55 @ X58))
% 0.44/0.66          | ((X57) != (k1_tarski @ X55)))),
% 0.44/0.66      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.44/0.66  thf('5', plain,
% 0.44/0.66      (![X55 : $i, X58 : $i]:
% 0.44/0.66         (r1_tarski @ (k1_tarski @ X55) @ (k2_tarski @ X55 @ X58))),
% 0.44/0.66      inference('simplify', [status(thm)], ['4'])).
% 0.44/0.66  thf(t1_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.44/0.66       ( r1_tarski @ A @ C ) ))).
% 0.44/0.66  thf('6', plain,
% 0.44/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.66         (~ (r1_tarski @ X8 @ X9)
% 0.44/0.66          | ~ (r1_tarski @ X9 @ X10)
% 0.44/0.66          | (r1_tarski @ X8 @ X10))),
% 0.44/0.66      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.44/0.66  thf('7', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         ((r1_tarski @ (k1_tarski @ X1) @ X2)
% 0.44/0.66          | ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.44/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.66  thf('8', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         (~ (r1_tarski @ (k1_enumset1 @ X1 @ X1 @ X0) @ X2)
% 0.44/0.66          | (r1_tarski @ (k1_tarski @ X1) @ X2))),
% 0.44/0.66      inference('sup-', [status(thm)], ['3', '7'])).
% 0.44/0.66  thf('9', plain,
% 0.44/0.66      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.44/0.66      inference('sup-', [status(thm)], ['2', '8'])).
% 0.44/0.66  thf(t28_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.44/0.66  thf('10', plain,
% 0.44/0.66      (![X11 : $i, X12 : $i]:
% 0.44/0.66         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 0.44/0.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.66  thf('11', plain,
% 0.44/0.66      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.44/0.66         = (k1_tarski @ sk_A))),
% 0.44/0.66      inference('sup-', [status(thm)], ['9', '10'])).
% 0.44/0.66  thf(l38_zfmisc_1, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.44/0.66       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.44/0.66         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.44/0.66  thf('12', plain,
% 0.44/0.66      (![X51 : $i, X53 : $i, X54 : $i]:
% 0.44/0.66         (((k4_xboole_0 @ (k2_tarski @ X51 @ X53) @ X54) = (k1_tarski @ X51))
% 0.44/0.66          | ((X51) != (X53))
% 0.44/0.66          | (r2_hidden @ X51 @ X54))),
% 0.44/0.66      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.44/0.66  thf('13', plain,
% 0.44/0.66      (![X53 : $i, X54 : $i]:
% 0.44/0.66         ((r2_hidden @ X53 @ X54)
% 0.44/0.66          | ((k4_xboole_0 @ (k2_tarski @ X53 @ X53) @ X54) = (k1_tarski @ X53)))),
% 0.44/0.66      inference('simplify', [status(thm)], ['12'])).
% 0.44/0.66  thf(t69_enumset1, axiom,
% 0.44/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.44/0.66  thf('14', plain,
% 0.44/0.66      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.44/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.66  thf('15', plain,
% 0.44/0.66      (![X53 : $i, X54 : $i]:
% 0.44/0.66         ((r2_hidden @ X53 @ X54)
% 0.44/0.66          | ((k4_xboole_0 @ (k1_tarski @ X53) @ X54) = (k1_tarski @ X53)))),
% 0.44/0.66      inference('demod', [status(thm)], ['13', '14'])).
% 0.44/0.66  thf(t48_xboole_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.66  thf('16', plain,
% 0.44/0.66      (![X13 : $i, X14 : $i]:
% 0.44/0.66         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.44/0.66           = (k3_xboole_0 @ X13 @ X14))),
% 0.44/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.66  thf('17', plain,
% 0.44/0.66      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.44/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.66  thf('18', plain,
% 0.44/0.66      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X51 @ X52)
% 0.44/0.66          | ((k4_xboole_0 @ (k2_tarski @ X51 @ X53) @ X52) != (k1_tarski @ X51)))),
% 0.44/0.66      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.44/0.66  thf('19', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0))
% 0.44/0.66          | ~ (r2_hidden @ X0 @ X1))),
% 0.44/0.66      inference('sup-', [status(thm)], ['17', '18'])).
% 0.44/0.66  thf('20', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (((k3_xboole_0 @ (k1_tarski @ X1) @ X0) != (k1_tarski @ X1))
% 0.44/0.66          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['16', '19'])).
% 0.44/0.66  thf('21', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.44/0.66          | (r2_hidden @ X0 @ X1)
% 0.44/0.66          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['15', '20'])).
% 0.44/0.66  thf('22', plain,
% 0.44/0.66      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.44/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.66  thf(d2_tarski, axiom,
% 0.44/0.66    (![A:$i,B:$i,C:$i]:
% 0.44/0.66     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.44/0.66       ( ![D:$i]:
% 0.44/0.66         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.44/0.66  thf('23', plain,
% 0.44/0.66      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.66         (((X18) != (X17))
% 0.44/0.66          | (r2_hidden @ X18 @ X19)
% 0.44/0.66          | ((X19) != (k2_tarski @ X20 @ X17)))),
% 0.44/0.66      inference('cnf', [status(esa)], [d2_tarski])).
% 0.44/0.66  thf('24', plain,
% 0.44/0.66      (![X17 : $i, X20 : $i]: (r2_hidden @ X17 @ (k2_tarski @ X20 @ X17))),
% 0.44/0.66      inference('simplify', [status(thm)], ['23'])).
% 0.44/0.66  thf('25', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.44/0.66      inference('sup+', [status(thm)], ['22', '24'])).
% 0.44/0.66  thf('26', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         ((r2_hidden @ X0 @ X1)
% 0.44/0.66          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0)))),
% 0.44/0.66      inference('demod', [status(thm)], ['21', '25'])).
% 0.44/0.66  thf('27', plain,
% 0.44/0.66      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.44/0.66        | (r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['11', '26'])).
% 0.44/0.66  thf('28', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.44/0.66      inference('simplify', [status(thm)], ['27'])).
% 0.44/0.66  thf('29', plain,
% 0.44/0.66      (![X17 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X21 @ X19)
% 0.44/0.66          | ((X21) = (X20))
% 0.44/0.66          | ((X21) = (X17))
% 0.44/0.66          | ((X19) != (k2_tarski @ X20 @ X17)))),
% 0.44/0.66      inference('cnf', [status(esa)], [d2_tarski])).
% 0.44/0.66  thf('30', plain,
% 0.44/0.66      (![X17 : $i, X20 : $i, X21 : $i]:
% 0.44/0.66         (((X21) = (X17))
% 0.44/0.66          | ((X21) = (X20))
% 0.44/0.66          | ~ (r2_hidden @ X21 @ (k2_tarski @ X20 @ X17)))),
% 0.44/0.66      inference('simplify', [status(thm)], ['29'])).
% 0.44/0.66  thf('31', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_D_1)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['28', '30'])).
% 0.44/0.66  thf('32', plain, (((sk_A) != (sk_D_1))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('33', plain, (((sk_A) != (sk_C_1))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('34', plain, ($false),
% 0.44/0.66      inference('simplify_reflect-', [status(thm)], ['31', '32', '33'])).
% 0.44/0.66  
% 0.44/0.66  % SZS output end Refutation
% 0.44/0.66  
% 0.44/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
