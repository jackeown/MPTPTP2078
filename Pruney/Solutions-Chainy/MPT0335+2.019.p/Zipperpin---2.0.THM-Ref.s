%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RLY3v6jI8u

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:15 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  338 ( 567 expanded)
%              Number of equality atoms :   35 (  60 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k3_xboole_0 @ X40 @ ( k1_tarski @ X39 ) )
        = ( k1_tarski @ X39 ) )
      | ~ ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ! [D: $i] :
            ( ( ( r1_tarski @ D @ B )
              & ( r1_tarski @ D @ C ) )
           => ( r1_tarski @ D @ A ) ) )
     => ( A
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ( r1_tarski @ ( sk_D @ X10 @ X9 @ X8 ) @ X10 )
      | ( X8
        = ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ sk_B @ X0 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ ( sk_D @ sk_A @ sk_B @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ~ ( r1_tarski @ ( sk_D @ X10 @ X9 @ X8 ) @ X8 )
      | ( X8
        = ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('10',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('12',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( sk_A
      = ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['13'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = ( k3_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup+',[status(thm)],['2','24'])).

thf('26',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RLY3v6jI8u
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:20:48 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.59/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.78  % Solved by: fo/fo7.sh
% 0.59/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.78  % done 178 iterations in 0.328s
% 0.59/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.78  % SZS output start Refutation
% 0.59/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.78  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.59/0.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.78  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.59/0.78  thf(t148_zfmisc_1, conjecture,
% 0.59/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.78     ( ( ( r1_tarski @ A @ B ) & 
% 0.59/0.78         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.59/0.78         ( r2_hidden @ D @ A ) ) =>
% 0.59/0.78       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.59/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.78    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.78        ( ( ( r1_tarski @ A @ B ) & 
% 0.59/0.78            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.59/0.78            ( r2_hidden @ D @ A ) ) =>
% 0.59/0.78          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.59/0.78    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.59/0.78  thf('0', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(l31_zfmisc_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( r2_hidden @ A @ B ) =>
% 0.59/0.78       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.59/0.78  thf('1', plain,
% 0.59/0.78      (![X39 : $i, X40 : $i]:
% 0.59/0.78         (((k3_xboole_0 @ X40 @ (k1_tarski @ X39)) = (k1_tarski @ X39))
% 0.59/0.78          | ~ (r2_hidden @ X39 @ X40))),
% 0.59/0.78      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.59/0.78  thf('2', plain,
% 0.59/0.78      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)) = (k1_tarski @ sk_D_1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.78  thf(d10_xboole_0, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.78  thf('3', plain,
% 0.59/0.78      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.79  thf('4', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.59/0.79      inference('simplify', [status(thm)], ['3'])).
% 0.59/0.79  thf('5', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(t20_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.59/0.79         ( ![D:$i]:
% 0.59/0.79           ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 0.59/0.79             ( r1_tarski @ D @ A ) ) ) ) =>
% 0.59/0.79       ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.59/0.79  thf('6', plain,
% 0.59/0.79      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.59/0.79         (~ (r1_tarski @ X8 @ X9)
% 0.59/0.79          | ~ (r1_tarski @ X8 @ X10)
% 0.59/0.79          | (r1_tarski @ (sk_D @ X10 @ X9 @ X8) @ X10)
% 0.59/0.79          | ((X8) = (k3_xboole_0 @ X9 @ X10)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.59/0.79  thf('7', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (((sk_A) = (k3_xboole_0 @ sk_B @ X0))
% 0.59/0.79          | (r1_tarski @ (sk_D @ X0 @ sk_B @ sk_A) @ X0)
% 0.59/0.79          | ~ (r1_tarski @ sk_A @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      (((r1_tarski @ (sk_D @ sk_A @ sk_B @ sk_A) @ sk_A)
% 0.59/0.79        | ((sk_A) = (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['4', '7'])).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.59/0.79         (~ (r1_tarski @ X8 @ X9)
% 0.59/0.79          | ~ (r1_tarski @ X8 @ X10)
% 0.59/0.79          | ~ (r1_tarski @ (sk_D @ X10 @ X9 @ X8) @ X8)
% 0.59/0.79          | ((X8) = (k3_xboole_0 @ X9 @ X10)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.59/0.79  thf('10', plain,
% 0.59/0.79      ((((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.59/0.79        | ((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.59/0.79        | ~ (r1_tarski @ sk_A @ sk_A)
% 0.59/0.79        | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.59/0.79      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.79  thf('11', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.59/0.79      inference('simplify', [status(thm)], ['3'])).
% 0.59/0.79  thf('12', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('13', plain,
% 0.59/0.79      ((((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.59/0.79        | ((sk_A) = (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.59/0.79  thf('14', plain, (((sk_A) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.59/0.79      inference('simplify', [status(thm)], ['13'])).
% 0.59/0.79  thf(commutativity_k3_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.79  thf(t16_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.59/0.79       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.59/0.79  thf('16', plain,
% 0.59/0.79      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.59/0.79         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.59/0.79           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.59/0.79  thf('17', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.79  thf('18', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 0.59/0.79           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X2 @ X0))
% 0.59/0.79           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['15', '18'])).
% 0.59/0.79  thf('20', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A))
% 0.59/0.79           = (k3_xboole_0 @ X0 @ sk_A))),
% 0.59/0.79      inference('sup+', [status(thm)], ['14', '19'])).
% 0.59/0.79  thf('21', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D_1))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('22', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 0.59/0.79           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.79  thf('23', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((k3_xboole_0 @ X0 @ (k1_tarski @ sk_D_1))
% 0.59/0.79           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.79  thf('24', plain,
% 0.59/0.79      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1))
% 0.59/0.79         = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.59/0.79      inference('sup+', [status(thm)], ['20', '23'])).
% 0.59/0.79  thf('25', plain, (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C @ sk_A))),
% 0.59/0.79      inference('sup+', [status(thm)], ['2', '24'])).
% 0.59/0.79  thf('26', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D_1))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('27', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.59/0.79  thf('28', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D_1))),
% 0.59/0.79      inference('demod', [status(thm)], ['26', '27'])).
% 0.59/0.79  thf('29', plain, ($false),
% 0.59/0.79      inference('simplify_reflect-', [status(thm)], ['25', '28'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.59/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
