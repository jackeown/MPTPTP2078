%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MAPIvfAlcf

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:05 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   50 (  57 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  312 ( 377 expanded)
%              Number of equality atoms :   22 (  27 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ ( k1_tarski @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('6',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X27 ) @ X29 )
      | ~ ( r2_hidden @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('10',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
    | ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['12','19'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = sk_B ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_tarski @ X16 @ X15 )
      = ( k2_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != sk_B ),
    inference(demod,[status(thm)],['23','28'])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MAPIvfAlcf
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 14:10:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.52  % Solved by: fo/fo7.sh
% 0.18/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.52  % done 171 iterations in 0.082s
% 0.18/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.52  % SZS output start Refutation
% 0.18/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.18/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.18/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.18/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.18/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.18/0.52  thf(t46_zfmisc_1, conjecture,
% 0.18/0.52    (![A:$i,B:$i]:
% 0.18/0.52     ( ( r2_hidden @ A @ B ) =>
% 0.18/0.52       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.18/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.52    (~( ![A:$i,B:$i]:
% 0.18/0.52        ( ( r2_hidden @ A @ B ) =>
% 0.18/0.52          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.18/0.52    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.18/0.52  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.18/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.52  thf(d10_xboole_0, axiom,
% 0.18/0.52    (![A:$i,B:$i]:
% 0.18/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.18/0.52  thf('1', plain,
% 0.18/0.52      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.18/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.52  thf('2', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.18/0.52      inference('simplify', [status(thm)], ['1'])).
% 0.18/0.52  thf(l1_zfmisc_1, axiom,
% 0.18/0.52    (![A:$i,B:$i]:
% 0.18/0.52     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.18/0.52  thf('3', plain,
% 0.18/0.52      (![X27 : $i, X28 : $i]:
% 0.18/0.52         ((r2_hidden @ X27 @ X28) | ~ (r1_tarski @ (k1_tarski @ X27) @ X28))),
% 0.18/0.52      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.18/0.52  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.18/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.52  thf(d4_xboole_0, axiom,
% 0.18/0.52    (![A:$i,B:$i,C:$i]:
% 0.18/0.52     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.18/0.52       ( ![D:$i]:
% 0.18/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.18/0.52           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.18/0.52  thf('5', plain,
% 0.18/0.52      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.18/0.52         (~ (r2_hidden @ X4 @ X5)
% 0.18/0.52          | ~ (r2_hidden @ X4 @ X6)
% 0.18/0.52          | (r2_hidden @ X4 @ X7)
% 0.18/0.52          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.18/0.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.18/0.52  thf('6', plain,
% 0.18/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.18/0.52         ((r2_hidden @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 0.18/0.52          | ~ (r2_hidden @ X4 @ X6)
% 0.18/0.52          | ~ (r2_hidden @ X4 @ X5))),
% 0.18/0.52      inference('simplify', [status(thm)], ['5'])).
% 0.18/0.52  thf('7', plain,
% 0.18/0.52      (![X0 : $i, X1 : $i]:
% 0.18/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.18/0.52          | (r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 0.18/0.52      inference('sup-', [status(thm)], ['4', '6'])).
% 0.18/0.52  thf('8', plain,
% 0.18/0.52      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.18/0.52      inference('sup-', [status(thm)], ['0', '7'])).
% 0.18/0.52  thf('9', plain,
% 0.18/0.52      (![X27 : $i, X29 : $i]:
% 0.18/0.52         ((r1_tarski @ (k1_tarski @ X27) @ X29) | ~ (r2_hidden @ X27 @ X29))),
% 0.18/0.52      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.18/0.52  thf('10', plain,
% 0.18/0.52      ((r1_tarski @ (k1_tarski @ sk_A) @ 
% 0.18/0.52        (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.18/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.18/0.52  thf('11', plain,
% 0.18/0.52      (![X10 : $i, X12 : $i]:
% 0.18/0.52         (((X10) = (X12))
% 0.18/0.52          | ~ (r1_tarski @ X12 @ X10)
% 0.18/0.52          | ~ (r1_tarski @ X10 @ X12))),
% 0.18/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.52  thf('12', plain,
% 0.18/0.52      ((~ (r1_tarski @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.18/0.52           (k1_tarski @ sk_A))
% 0.18/0.52        | ((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))),
% 0.18/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.18/0.52  thf(d3_tarski, axiom,
% 0.18/0.52    (![A:$i,B:$i]:
% 0.18/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.18/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.18/0.52  thf('13', plain,
% 0.18/0.52      (![X1 : $i, X3 : $i]:
% 0.18/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.18/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.18/0.52  thf('14', plain,
% 0.18/0.52      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.18/0.52         (~ (r2_hidden @ X8 @ X7)
% 0.18/0.52          | (r2_hidden @ X8 @ X6)
% 0.18/0.52          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.18/0.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.18/0.52  thf('15', plain,
% 0.18/0.52      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.18/0.52         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.18/0.52      inference('simplify', [status(thm)], ['14'])).
% 0.18/0.52  thf('16', plain,
% 0.18/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.52         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.18/0.52          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.18/0.52      inference('sup-', [status(thm)], ['13', '15'])).
% 0.18/0.52  thf('17', plain,
% 0.18/0.52      (![X1 : $i, X3 : $i]:
% 0.18/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.18/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.18/0.52  thf('18', plain,
% 0.18/0.52      (![X0 : $i, X1 : $i]:
% 0.18/0.52         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.18/0.52          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.18/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.18/0.52  thf('19', plain,
% 0.18/0.52      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.18/0.52      inference('simplify', [status(thm)], ['18'])).
% 0.18/0.52  thf('20', plain,
% 0.18/0.52      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.18/0.52      inference('demod', [status(thm)], ['12', '19'])).
% 0.18/0.52  thf(t22_xboole_1, axiom,
% 0.18/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.18/0.52  thf('21', plain,
% 0.18/0.52      (![X13 : $i, X14 : $i]:
% 0.18/0.52         ((k2_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)) = (X13))),
% 0.18/0.52      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.18/0.52  thf('22', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))),
% 0.18/0.52      inference('sup+', [status(thm)], ['20', '21'])).
% 0.18/0.52  thf('23', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (sk_B))),
% 0.18/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.52  thf(commutativity_k2_tarski, axiom,
% 0.18/0.52    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.18/0.52  thf('24', plain,
% 0.18/0.52      (![X15 : $i, X16 : $i]:
% 0.18/0.52         ((k2_tarski @ X16 @ X15) = (k2_tarski @ X15 @ X16))),
% 0.18/0.52      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.18/0.52  thf(l51_zfmisc_1, axiom,
% 0.18/0.52    (![A:$i,B:$i]:
% 0.18/0.52     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.18/0.52  thf('25', plain,
% 0.18/0.52      (![X30 : $i, X31 : $i]:
% 0.18/0.52         ((k3_tarski @ (k2_tarski @ X30 @ X31)) = (k2_xboole_0 @ X30 @ X31))),
% 0.18/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.18/0.52  thf('26', plain,
% 0.18/0.52      (![X0 : $i, X1 : $i]:
% 0.18/0.52         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.18/0.52      inference('sup+', [status(thm)], ['24', '25'])).
% 0.18/0.52  thf('27', plain,
% 0.18/0.52      (![X30 : $i, X31 : $i]:
% 0.18/0.52         ((k3_tarski @ (k2_tarski @ X30 @ X31)) = (k2_xboole_0 @ X30 @ X31))),
% 0.18/0.52      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.18/0.52  thf('28', plain,
% 0.18/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.18/0.52      inference('sup+', [status(thm)], ['26', '27'])).
% 0.18/0.52  thf('29', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (sk_B))),
% 0.18/0.52      inference('demod', [status(thm)], ['23', '28'])).
% 0.18/0.52  thf('30', plain, ($false),
% 0.18/0.52      inference('simplify_reflect-', [status(thm)], ['22', '29'])).
% 0.18/0.52  
% 0.18/0.52  % SZS output end Refutation
% 0.18/0.52  
% 0.18/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
