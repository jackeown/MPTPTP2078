%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u4rdHz073W

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:19 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   44 (  57 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  353 ( 559 expanded)
%              Number of equality atoms :   31 (  50 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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

thf('0',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k3_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('9',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('10',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X19 ) @ X21 )
      | ~ ( r2_hidden @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('11',plain,(
    r1_tarski @ ( k1_tarski @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_D_1 ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_D_1 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_D_1 ) @ ( k1_tarski @ sk_D_1 ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['7'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) )
    | ( ( k1_tarski @ sk_D_1 )
      = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['6','25'])).

thf('27',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u4rdHz073W
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.36/1.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.36/1.54  % Solved by: fo/fo7.sh
% 1.36/1.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.36/1.54  % done 1494 iterations in 1.082s
% 1.36/1.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.36/1.54  % SZS output start Refutation
% 1.36/1.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.36/1.54  thf(sk_B_type, type, sk_B: $i).
% 1.36/1.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.36/1.54  thf(sk_C_type, type, sk_C: $i).
% 1.36/1.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.36/1.54  thf(sk_A_type, type, sk_A: $i).
% 1.36/1.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.36/1.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.36/1.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.36/1.54  thf(t148_zfmisc_1, conjecture,
% 1.36/1.54    (![A:$i,B:$i,C:$i,D:$i]:
% 1.36/1.54     ( ( ( r1_tarski @ A @ B ) & 
% 1.36/1.54         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.36/1.54         ( r2_hidden @ D @ A ) ) =>
% 1.36/1.54       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 1.36/1.54  thf(zf_stmt_0, negated_conjecture,
% 1.36/1.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.36/1.54        ( ( ( r1_tarski @ A @ B ) & 
% 1.36/1.54            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.36/1.54            ( r2_hidden @ D @ A ) ) =>
% 1.36/1.54          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 1.36/1.54    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 1.36/1.54  thf('0', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D_1))),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf(t28_xboole_1, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.36/1.54  thf('2', plain,
% 1.36/1.54      (![X9 : $i, X10 : $i]:
% 1.36/1.54         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 1.36/1.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.36/1.54  thf('3', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 1.36/1.54      inference('sup-', [status(thm)], ['1', '2'])).
% 1.36/1.54  thf(t16_xboole_1, axiom,
% 1.36/1.54    (![A:$i,B:$i,C:$i]:
% 1.36/1.54     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.36/1.54       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.36/1.54  thf('4', plain,
% 1.36/1.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.36/1.54         ((k3_xboole_0 @ (k3_xboole_0 @ X6 @ X7) @ X8)
% 1.36/1.54           = (k3_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8)))),
% 1.36/1.54      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.36/1.54  thf('5', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((k3_xboole_0 @ sk_A @ X0)
% 1.36/1.54           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 1.36/1.54      inference('sup+', [status(thm)], ['3', '4'])).
% 1.36/1.54  thf('6', plain,
% 1.36/1.54      (((k3_xboole_0 @ sk_A @ sk_C)
% 1.36/1.54         = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 1.36/1.54      inference('sup+', [status(thm)], ['0', '5'])).
% 1.36/1.54  thf(d4_xboole_0, axiom,
% 1.36/1.54    (![A:$i,B:$i,C:$i]:
% 1.36/1.54     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.36/1.54       ( ![D:$i]:
% 1.36/1.54         ( ( r2_hidden @ D @ C ) <=>
% 1.36/1.54           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.36/1.54  thf('7', plain,
% 1.36/1.54      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.36/1.54         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.36/1.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.36/1.54          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.36/1.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.36/1.54  thf('8', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.36/1.54          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.36/1.54      inference('eq_fact', [status(thm)], ['7'])).
% 1.36/1.54  thf('9', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf(l1_zfmisc_1, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.36/1.54  thf('10', plain,
% 1.36/1.54      (![X19 : $i, X21 : $i]:
% 1.36/1.54         ((r1_tarski @ (k1_tarski @ X19) @ X21) | ~ (r2_hidden @ X19 @ X21))),
% 1.36/1.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.36/1.54  thf('11', plain, ((r1_tarski @ (k1_tarski @ sk_D_1) @ sk_A)),
% 1.36/1.54      inference('sup-', [status(thm)], ['9', '10'])).
% 1.36/1.54  thf('12', plain,
% 1.36/1.54      (![X9 : $i, X10 : $i]:
% 1.36/1.54         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 1.36/1.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.36/1.54  thf('13', plain,
% 1.36/1.54      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A) = (k1_tarski @ sk_D_1))),
% 1.36/1.54      inference('sup-', [status(thm)], ['11', '12'])).
% 1.36/1.54  thf('14', plain,
% 1.36/1.54      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.36/1.54         (~ (r2_hidden @ X4 @ X3)
% 1.36/1.54          | (r2_hidden @ X4 @ X2)
% 1.36/1.54          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 1.36/1.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.36/1.54  thf('15', plain,
% 1.36/1.54      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.36/1.54         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.36/1.54      inference('simplify', [status(thm)], ['14'])).
% 1.36/1.54  thf('16', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_D_1)) | (r2_hidden @ X0 @ sk_A))),
% 1.36/1.54      inference('sup-', [status(thm)], ['13', '15'])).
% 1.36/1.54  thf('17', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D_1)))
% 1.36/1.54          | (r2_hidden @ 
% 1.36/1.54             (sk_D @ (k1_tarski @ sk_D_1) @ (k1_tarski @ sk_D_1) @ X0) @ sk_A))),
% 1.36/1.54      inference('sup-', [status(thm)], ['8', '16'])).
% 1.36/1.54  thf('18', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.36/1.54          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.36/1.54      inference('eq_fact', [status(thm)], ['7'])).
% 1.36/1.54  thf('19', plain,
% 1.36/1.54      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.36/1.54         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.36/1.54          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.36/1.54          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.36/1.54          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.36/1.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.36/1.54  thf('20', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.36/1.54          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.36/1.54          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.36/1.54          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['18', '19'])).
% 1.36/1.54  thf('21', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.36/1.54          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.36/1.54          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.36/1.54      inference('simplify', [status(thm)], ['20'])).
% 1.36/1.54  thf('22', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.36/1.54          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.36/1.54      inference('eq_fact', [status(thm)], ['7'])).
% 1.36/1.54  thf('23', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.36/1.54          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.36/1.54      inference('clc', [status(thm)], ['21', '22'])).
% 1.36/1.54  thf('24', plain,
% 1.36/1.54      ((((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))
% 1.36/1.54        | ((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1))))),
% 1.36/1.54      inference('sup-', [status(thm)], ['17', '23'])).
% 1.36/1.54  thf('25', plain,
% 1.36/1.54      (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)))),
% 1.36/1.54      inference('simplify', [status(thm)], ['24'])).
% 1.36/1.54  thf('26', plain, (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_A @ sk_C))),
% 1.36/1.54      inference('sup+', [status(thm)], ['6', '25'])).
% 1.36/1.54  thf('27', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D_1))),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf('28', plain, ($false),
% 1.36/1.54      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 1.36/1.54  
% 1.36/1.54  % SZS output end Refutation
% 1.36/1.54  
% 1.36/1.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
