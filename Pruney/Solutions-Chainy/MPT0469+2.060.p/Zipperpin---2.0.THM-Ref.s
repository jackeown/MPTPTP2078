%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YfMxcocZuQ

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 (  99 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  266 ( 614 expanded)
%              Number of equality atoms :   36 (  81 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('0',plain,(
    ! [X48: $i,X51: $i] :
      ( ( X51
        = ( k2_relat_1 @ X48 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X51 @ X48 ) @ ( sk_C_1 @ X51 @ X48 ) ) @ X48 )
      | ( r2_hidden @ ( sk_C_1 @ X51 @ X48 ) @ X51 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('5',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33 != X35 )
      | ~ ( r2_hidden @ X33 @ ( k4_xboole_0 @ X34 @ ( k1_tarski @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('6',plain,(
    ! [X34: $i,X35: $i] :
      ~ ( r2_hidden @ X35 @ ( k4_xboole_0 @ X34 @ ( k1_tarski @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('13',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('14',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('16',plain,(
    ! [X41: $i,X44: $i] :
      ( ( X44
        = ( k1_relat_1 @ X41 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X44 @ X41 ) @ ( sk_D @ X44 @ X41 ) ) @ X41 )
      | ( r2_hidden @ ( sk_C @ X44 @ X41 ) @ X44 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('20',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('22',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('25',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['23','24'])).

thf('26',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['15','25'])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['13','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YfMxcocZuQ
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 94 iterations in 0.044s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(d5_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.49           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X48 : $i, X51 : $i]:
% 0.20/0.49         (((X51) = (k2_relat_1 @ X48))
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ (sk_D_2 @ X51 @ X48) @ (sk_C_1 @ X51 @ X48)) @ X48)
% 0.20/0.49          | (r2_hidden @ (sk_C_1 @ X51 @ X48) @ X51))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.49  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.49  thf('1', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.49  thf(t100_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X2 : $i, X3 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ X2 @ X3)
% 0.20/0.49           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf(t69_enumset1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.49  thf('4', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf(t64_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.20/0.49       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.49         (((X33) != (X35))
% 0.20/0.49          | ~ (r2_hidden @ X33 @ (k4_xboole_0 @ X34 @ (k1_tarski @ X35))))),
% 0.20/0.49      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X34 : $i, X35 : $i]:
% 0.20/0.49         ~ (r2_hidden @ X35 @ (k4_xboole_0 @ X34 @ (k1_tarski @ X35)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ~ (r2_hidden @ X0 @ 
% 0.20/0.49            (k5_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k2_tarski @ X0 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '7'])).
% 0.20/0.49  thf(t92_xboole_1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('9', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.49  thf('10', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.20/0.49          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '10'])).
% 0.20/0.49  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('13', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf(t60_relat_1, conjecture,
% 0.20/0.49    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.49     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.49        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.49         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.49      inference('split', [status(esa)], ['14'])).
% 0.20/0.49  thf(d4_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.49           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X41 : $i, X44 : $i]:
% 0.20/0.49         (((X44) = (k1_relat_1 @ X41))
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ (sk_C @ X44 @ X41) @ (sk_D @ X44 @ X41)) @ X41)
% 0.20/0.49          | (r2_hidden @ (sk_C @ X44 @ X41) @ X44))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.49  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.20/0.49          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('20', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.49         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.49      inference('split', [status(esa)], ['14'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.49         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('23', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.20/0.49       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.49      inference('split', [status(esa)], ['14'])).
% 0.20/0.49  thf('25', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['15', '25'])).
% 0.20/0.49  thf('27', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['13', '26'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
