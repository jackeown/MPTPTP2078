%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t2AOTbs43G

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 146 expanded)
%              Number of leaves         :   19 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :  480 (1165 expanded)
%              Number of equality atoms :   89 ( 221 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('0',plain,(
    ! [X41: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X41 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ( X7 = X6 )
      | ( X7 = X3 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('3',plain,(
    ! [X3: $i,X6: $i,X7: $i] :
      ( ( X7 = X3 )
      | ( X7 = X6 )
      | ~ ( r2_hidden @ X7 @ ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('9',plain,(
    ! [X3: $i,X6: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X6 @ X3 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('11',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_2 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('13',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X38 @ X39 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('14',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_2 ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X38: $i,X40: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X38 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('17',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_2 ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('21',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_2 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ ( k2_mcart_1 @ sk_A ) ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( r2_hidden @ X43 @ X41 )
      | ( ( sk_B_1 @ X41 )
       != ( k4_tarski @ X43 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B_1 @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('26',plain,
    ( ( ( sk_A != sk_A )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('30',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('31',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('32',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_2 ),
    inference('sup+',[status(thm)],['15','16'])).

thf('33',plain,
    ( sk_A
    = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_A
      = ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( r2_hidden @ X42 @ X41 )
      | ( ( sk_B_1 @ X41 )
       != ( k4_tarski @ X43 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B_1 @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B_1 @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,
    ( ( ( sk_A != sk_A )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','37'])).

thf('39',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('41',plain,(
    ! [X3: $i,X6: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X6 @ X3 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('49',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['27','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t2AOTbs43G
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:54:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 86 iterations in 0.057s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.50  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.50  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.50  thf(t9_mcart_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.50                 ( ![C:$i,D:$i]:
% 0.20/0.50                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.20/0.50                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X41 : $i]:
% 0.20/0.50         (((X41) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X41) @ X41))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.50  thf(t69_enumset1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.50  thf('1', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf(d2_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.50       ( ![D:$i]:
% 0.20/0.50         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X3 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X7 @ X5)
% 0.20/0.50          | ((X7) = (X6))
% 0.20/0.50          | ((X7) = (X3))
% 0.20/0.50          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X3 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         (((X7) = (X3))
% 0.20/0.50          | ((X7) = (X6))
% 0.20/0.50          | ~ (r2_hidden @ X7 @ (k2_tarski @ X6 @ X3)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.50          | ((sk_B_1 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.50  thf('7', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (((X4) != (X3))
% 0.20/0.50          | (r2_hidden @ X4 @ X5)
% 0.20/0.50          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X3 : $i, X6 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X6 @ X3))),
% 0.20/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.50  thf('10', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['7', '9'])).
% 0.20/0.50  thf(t20_mcart_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.50       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.50          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.20/0.50  thf('11', plain, (((sk_A) = (k4_tarski @ sk_B_2 @ sk_C_2))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('12', plain, (((sk_A) = (k4_tarski @ sk_B_2 @ sk_C_2))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t7_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.50       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X38 : $i, X39 : $i]: ((k1_mcart_1 @ (k4_tarski @ X38 @ X39)) = (X38))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.50  thf('14', plain, (((k1_mcart_1 @ sk_A) = (sk_B_2))),
% 0.20/0.50      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_2))),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X38 : $i, X40 : $i]: ((k2_mcart_1 @ (k4_tarski @ X38 @ X40)) = (X40))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.50  thf('17', plain, (((k2_mcart_1 @ sk_A) = (sk_C_2))),
% 0.20/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('split', [status(esa)], ['18'])).
% 0.20/0.50  thf('20', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_2))),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_2)))
% 0.20/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      ((((sk_A) = (k4_tarski @ sk_A @ (k2_mcart_1 @ sk_A))))
% 0.20/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['17', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.50         (((X41) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X43 @ X41)
% 0.20/0.50          | ((sk_B_1 @ X41) != (k4_tarski @ X43 @ X42)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((sk_B_1 @ X0) != (sk_A))
% 0.20/0.50           | ~ (r2_hidden @ sk_A @ X0)
% 0.20/0.50           | ((X0) = (k1_xboole_0))))
% 0.20/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.50         | ((sk_B_1 @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.20/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((((sk_A) != (sk_A))
% 0.20/0.50         | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.50         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.20/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.50         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.50          | ((sk_B_1 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.50  thf('29', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['7', '9'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('split', [status(esa)], ['18'])).
% 0.20/0.50  thf('31', plain, (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_C_2))),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.50  thf('32', plain, (((k2_mcart_1 @ sk_A) = (sk_C_2))),
% 0.20/0.50      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      ((((sk_A) = (k4_tarski @ (k1_mcart_1 @ sk_A) @ sk_A)))
% 0.20/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['30', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.50         (((X41) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X42 @ X41)
% 0.20/0.50          | ((sk_B_1 @ X41) != (k4_tarski @ X43 @ X42)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((sk_B_1 @ X0) != (sk_A))
% 0.20/0.50           | ~ (r2_hidden @ sk_A @ X0)
% 0.20/0.50           | ((X0) = (k1_xboole_0))))
% 0.20/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.50         | ((sk_B_1 @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.20/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (((((sk_A) != (sk_A))
% 0.20/0.50         | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.20/0.50         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.20/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['28', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.20/0.50         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.50  thf('40', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X3 : $i, X6 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X6 @ X3))),
% 0.20/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.50  thf(d1_xboole_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf('44', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      ((~ (v1_xboole_0 @ k1_xboole_0)) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['39', '44'])).
% 0.20/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.50  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf('47', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['18'])).
% 0.20/0.50  thf('49', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('50', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['27', '49'])).
% 0.20/0.50  thf('51', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '43'])).
% 0.20/0.50  thf('52', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.50  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf('54', plain, ($false), inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
