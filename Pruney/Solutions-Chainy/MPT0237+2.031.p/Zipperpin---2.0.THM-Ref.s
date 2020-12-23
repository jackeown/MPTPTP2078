%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.roYkmBRApG

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:02 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   65 (  91 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  417 ( 669 expanded)
%              Number of equality atoms :   55 (  89 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) ) )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k2_tarski @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k5_xboole_0 @ ( k1_tarski @ X55 ) @ ( k1_tarski @ X56 ) )
        = ( k2_tarski @ X55 @ X56 ) )
      | ( X55 = X56 ) ) ),
    inference(cnf,[status(esa)],[t29_zfmisc_1])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X53 ) @ ( k1_tarski @ X54 ) )
      | ( X53 = X54 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X1 = X0 )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B_1 ) )
 != ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('12',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
     != ( k2_tarski @ sk_A @ sk_B_1 ) )
    | ( sk_A = sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_A = sk_B_1 ),
    inference(simplify,[status(thm)],['12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

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

thf('15',plain,(
    ! [X47: $i,X49: $i,X50: $i] :
      ( ( r1_tarski @ X49 @ ( k2_tarski @ X47 @ X50 ) )
      | ( X49
       != ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('16',plain,(
    ! [X47: $i,X50: $i] :
      ( r1_tarski @ ( k1_tarski @ X47 ) @ ( k2_tarski @ X47 @ X50 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('22',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('24',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('29',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('32',plain,(
    sk_A = sk_B_1 ),
    inference(simplify,[status(thm)],['12'])).

thf('33',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    ( k1_tarski @ sk_A )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['2','13','31','32','33'])).

thf('35',plain,(
    $false ),
    inference(simplify,[status(thm)],['34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.roYkmBRApG
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:46:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 275 iterations in 0.107s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.56  thf(t32_zfmisc_1, conjecture,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.36/0.56       ( k2_tarski @ A @ B ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i,B:$i]:
% 0.36/0.56        ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) =
% 0.36/0.56          ( k2_tarski @ A @ B ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t32_zfmisc_1])).
% 0.36/0.56  thf('0', plain,
% 0.36/0.56      (((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1)))
% 0.36/0.56         != (k2_tarski @ sk_A @ sk_B_1))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(l51_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.56  thf('1', plain,
% 0.36/0.56      (![X51 : $i, X52 : $i]:
% 0.36/0.56         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.36/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.36/0.56         != (k2_tarski @ sk_A @ sk_B_1))),
% 0.36/0.56      inference('demod', [status(thm)], ['0', '1'])).
% 0.36/0.56  thf(t29_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( A ) != ( B ) ) =>
% 0.36/0.56       ( ( k5_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.36/0.56         ( k2_tarski @ A @ B ) ) ))).
% 0.36/0.56  thf('3', plain,
% 0.36/0.56      (![X55 : $i, X56 : $i]:
% 0.36/0.56         (((k5_xboole_0 @ (k1_tarski @ X55) @ (k1_tarski @ X56))
% 0.36/0.56            = (k2_tarski @ X55 @ X56))
% 0.36/0.56          | ((X55) = (X56)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t29_zfmisc_1])).
% 0.36/0.56  thf(t17_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( A ) != ( B ) ) =>
% 0.36/0.56       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.36/0.56  thf('4', plain,
% 0.36/0.56      (![X53 : $i, X54 : $i]:
% 0.36/0.56         ((r1_xboole_0 @ (k1_tarski @ X53) @ (k1_tarski @ X54))
% 0.36/0.56          | ((X53) = (X54)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.36/0.56  thf(t83_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      (![X14 : $i, X15 : $i]:
% 0.36/0.56         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.36/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.36/0.56  thf('6', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (((X1) = (X0))
% 0.36/0.56          | ((k4_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.36/0.56              = (k1_tarski @ X1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.56  thf(t98_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.36/0.56  thf('7', plain,
% 0.36/0.56      (![X17 : $i, X18 : $i]:
% 0.36/0.56         ((k2_xboole_0 @ X17 @ X18)
% 0.36/0.56           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.56  thf('8', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.36/0.56            = (k5_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))
% 0.36/0.56          | ((X0) = (X1)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['6', '7'])).
% 0.36/0.56  thf('9', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.36/0.56            = (k2_tarski @ X1 @ X0))
% 0.36/0.56          | ((X1) = (X0))
% 0.36/0.56          | ((X0) = (X1)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['3', '8'])).
% 0.36/0.56  thf('10', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (((X1) = (X0))
% 0.36/0.56          | ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.36/0.56              = (k2_tarski @ X1 @ X0)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['9'])).
% 0.36/0.56  thf('11', plain,
% 0.36/0.56      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B_1))
% 0.36/0.56         != (k2_tarski @ sk_A @ sk_B_1))),
% 0.36/0.56      inference('demod', [status(thm)], ['0', '1'])).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      ((((k2_tarski @ sk_A @ sk_B_1) != (k2_tarski @ sk_A @ sk_B_1))
% 0.36/0.56        | ((sk_A) = (sk_B_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.56  thf('13', plain, (((sk_A) = (sk_B_1))),
% 0.36/0.56      inference('simplify', [status(thm)], ['12'])).
% 0.36/0.56  thf(t69_enumset1, axiom,
% 0.36/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.36/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.56  thf(l45_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.36/0.56       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.36/0.56            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.36/0.56  thf('15', plain,
% 0.36/0.56      (![X47 : $i, X49 : $i, X50 : $i]:
% 0.36/0.56         ((r1_tarski @ X49 @ (k2_tarski @ X47 @ X50))
% 0.36/0.56          | ((X49) != (k1_tarski @ X47)))),
% 0.36/0.56      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.36/0.56  thf('16', plain,
% 0.36/0.56      (![X47 : $i, X50 : $i]:
% 0.36/0.56         (r1_tarski @ (k1_tarski @ X47) @ (k2_tarski @ X47 @ X50))),
% 0.36/0.56      inference('simplify', [status(thm)], ['15'])).
% 0.36/0.56  thf('17', plain,
% 0.36/0.56      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['14', '16'])).
% 0.36/0.56  thf(l32_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.56  thf('18', plain,
% 0.36/0.56      (![X7 : $i, X9 : $i]:
% 0.36/0.56         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.36/0.56      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.36/0.56  thf('19', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.56  thf('20', plain,
% 0.36/0.56      (![X17 : $i, X18 : $i]:
% 0.36/0.56         ((k2_xboole_0 @ X17 @ X18)
% 0.36/0.56           = (k5_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.36/0.56  thf('21', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.36/0.56           = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['19', '20'])).
% 0.36/0.56  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.36/0.56  thf('22', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.36/0.56  thf(t7_xboole_0, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.36/0.56  thf('23', plain,
% 0.36/0.56      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.36/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.36/0.56  thf(t4_xboole_0, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.36/0.56            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.56  thf('24', plain,
% 0.36/0.56      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.36/0.56          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.36/0.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.36/0.56  thf('25', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.56  thf('26', plain,
% 0.36/0.56      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['22', '25'])).
% 0.36/0.56  thf(t100_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.56  thf('27', plain,
% 0.36/0.56      (![X10 : $i, X11 : $i]:
% 0.36/0.56         ((k4_xboole_0 @ X10 @ X11)
% 0.36/0.56           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.56  thf('28', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['26', '27'])).
% 0.36/0.56  thf(t3_boole, axiom,
% 0.36/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.56  thf('29', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.36/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.56  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['28', '29'])).
% 0.36/0.56  thf('31', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.36/0.56           = (k1_tarski @ X0))),
% 0.36/0.56      inference('demod', [status(thm)], ['21', '30'])).
% 0.36/0.56  thf('32', plain, (((sk_A) = (sk_B_1))),
% 0.36/0.56      inference('simplify', [status(thm)], ['12'])).
% 0.36/0.56  thf('33', plain,
% 0.36/0.56      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 0.36/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.56  thf('34', plain, (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['2', '13', '31', '32', '33'])).
% 0.36/0.56  thf('35', plain, ($false), inference('simplify', [status(thm)], ['34'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.43/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
