%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p9qFwlpeiK

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:09 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 156 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  483 (1183 expanded)
%              Number of equality atoms :   94 ( 218 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ ( k1_tarski @ X27 ) )
        = X26 )
      | ( r2_hidden @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 != X18 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X18 ) )
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('6',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X18 ) @ ( k1_tarski @ X18 ) )
     != ( k1_tarski @ X18 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('8',plain,(
    ! [X18: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X18 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['4','8'])).

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

thf('10',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('11',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X30 @ X31 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('12',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( sk_A = sk_B_1 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33 = k1_xboole_0 )
      | ~ ( r2_hidden @ X35 @ X33 )
      | ( ( sk_B @ X33 )
       != ( k4_tarski @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X33: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X33 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X20 ) )
        = ( k1_tarski @ X19 ) )
      | ( X19 = X20 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X23 )
      | ~ ( r2_hidden @ X21 @ ( k4_xboole_0 @ X22 @ ( k1_tarski @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ~ ( r2_hidden @ X23 @ ( k4_xboole_0 @ X22 @ ( k1_tarski @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X18: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X18 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( sk_A != sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','28'])).

thf('30',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['4','8'])).

thf('32',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X30: $i,X32: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X30 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('34',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('36',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( sk_A
    = ( k4_tarski @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33 = k1_xboole_0 )
      | ~ ( r2_hidden @ X34 @ X33 )
      | ( ( sk_B @ X33 )
       != ( k4_tarski @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_A )
        | ~ ( r2_hidden @ sk_A @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_A ) )
       != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( X0
      = ( sk_B @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('43',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( sk_A != sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X18: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X18 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    sk_A
 != ( k2_mcart_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['13'])).

thf('49',plain,
    ( sk_A
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['30','49'])).

thf('51',plain,(
    ! [X18: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X18 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('52',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference(simplify,[status(thm)],['52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.p9qFwlpeiK
% 0.13/0.37  % Computer   : n019.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:49:53 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.24/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.55  % Solved by: fo/fo7.sh
% 0.24/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.55  % done 162 iterations in 0.064s
% 0.24/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.55  % SZS output start Refutation
% 0.24/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.24/0.55  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.24/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.24/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.24/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.24/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.55  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.24/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.55  thf(t65_zfmisc_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.24/0.55       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.24/0.55  thf('0', plain,
% 0.24/0.55      (![X26 : $i, X27 : $i]:
% 0.24/0.55         (((k4_xboole_0 @ X26 @ (k1_tarski @ X27)) = (X26))
% 0.24/0.55          | (r2_hidden @ X27 @ X26))),
% 0.24/0.55      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.24/0.55  thf(t1_boole, axiom,
% 0.24/0.55    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.24/0.55  thf('1', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.24/0.55      inference('cnf', [status(esa)], [t1_boole])).
% 0.24/0.55  thf(t46_xboole_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.24/0.55  thf('2', plain,
% 0.24/0.55      (![X4 : $i, X5 : $i]:
% 0.24/0.55         ((k4_xboole_0 @ X4 @ (k2_xboole_0 @ X4 @ X5)) = (k1_xboole_0))),
% 0.24/0.55      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.24/0.55  thf('3', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.24/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.24/0.55  thf('4', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.24/0.55          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.24/0.55      inference('sup+', [status(thm)], ['0', '3'])).
% 0.24/0.55  thf(t20_zfmisc_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.24/0.55         ( k1_tarski @ A ) ) <=>
% 0.24/0.55       ( ( A ) != ( B ) ) ))).
% 0.24/0.55  thf('5', plain,
% 0.24/0.55      (![X18 : $i, X19 : $i]:
% 0.24/0.55         (((X19) != (X18))
% 0.24/0.55          | ((k4_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X18))
% 0.24/0.55              != (k1_tarski @ X19)))),
% 0.24/0.55      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.24/0.55  thf('6', plain,
% 0.24/0.55      (![X18 : $i]:
% 0.24/0.55         ((k4_xboole_0 @ (k1_tarski @ X18) @ (k1_tarski @ X18))
% 0.24/0.55           != (k1_tarski @ X18))),
% 0.24/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.24/0.55  thf('7', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.24/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.24/0.55  thf('8', plain, (![X18 : $i]: ((k1_xboole_0) != (k1_tarski @ X18))),
% 0.24/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.24/0.55  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.24/0.55      inference('clc', [status(thm)], ['4', '8'])).
% 0.24/0.55  thf(t20_mcart_1, conjecture,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.24/0.55       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.24/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.55    (~( ![A:$i]:
% 0.24/0.55        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.24/0.55          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.24/0.55    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.24/0.55  thf('10', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf(t7_mcart_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.24/0.55       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.24/0.55  thf('11', plain,
% 0.24/0.55      (![X30 : $i, X31 : $i]: ((k1_mcart_1 @ (k4_tarski @ X30 @ X31)) = (X30))),
% 0.24/0.55      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.24/0.55  thf('12', plain, (((k1_mcart_1 @ sk_A) = (sk_B_1))),
% 0.24/0.55      inference('sup+', [status(thm)], ['10', '11'])).
% 0.24/0.55  thf('13', plain,
% 0.24/0.55      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('14', plain,
% 0.24/0.55      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.24/0.55      inference('split', [status(esa)], ['13'])).
% 0.24/0.55  thf('15', plain,
% 0.24/0.55      ((((sk_A) = (sk_B_1))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.24/0.55      inference('sup+', [status(thm)], ['12', '14'])).
% 0.24/0.55  thf('16', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('17', plain,
% 0.24/0.55      ((((sk_A) = (k4_tarski @ sk_A @ sk_C)))
% 0.24/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.24/0.55      inference('sup+', [status(thm)], ['15', '16'])).
% 0.24/0.55  thf(t9_mcart_1, axiom,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.55          ( ![B:$i]:
% 0.24/0.55            ( ~( ( r2_hidden @ B @ A ) & 
% 0.24/0.55                 ( ![C:$i,D:$i]:
% 0.24/0.55                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.24/0.55                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.24/0.55  thf('18', plain,
% 0.24/0.55      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.24/0.55         (((X33) = (k1_xboole_0))
% 0.24/0.55          | ~ (r2_hidden @ X35 @ X33)
% 0.24/0.55          | ((sk_B @ X33) != (k4_tarski @ X35 @ X34)))),
% 0.24/0.55      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.24/0.55  thf('19', plain,
% 0.24/0.55      ((![X0 : $i]:
% 0.24/0.55          (((sk_B @ X0) != (sk_A))
% 0.24/0.55           | ~ (r2_hidden @ sk_A @ X0)
% 0.24/0.55           | ((X0) = (k1_xboole_0))))
% 0.24/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.24/0.55  thf('20', plain,
% 0.24/0.55      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.24/0.55         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.24/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['9', '19'])).
% 0.24/0.55  thf('21', plain,
% 0.24/0.55      (![X33 : $i]:
% 0.24/0.55         (((X33) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X33) @ X33))),
% 0.24/0.55      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.24/0.55  thf('22', plain,
% 0.24/0.55      (![X19 : $i, X20 : $i]:
% 0.24/0.55         (((k4_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X20))
% 0.24/0.55            = (k1_tarski @ X19))
% 0.24/0.55          | ((X19) = (X20)))),
% 0.24/0.55      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.24/0.55  thf(t64_zfmisc_1, axiom,
% 0.24/0.55    (![A:$i,B:$i,C:$i]:
% 0.24/0.55     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.24/0.55       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.24/0.55  thf('23', plain,
% 0.24/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.24/0.55         (((X21) != (X23))
% 0.24/0.55          | ~ (r2_hidden @ X21 @ (k4_xboole_0 @ X22 @ (k1_tarski @ X23))))),
% 0.24/0.55      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.24/0.55  thf('24', plain,
% 0.24/0.55      (![X22 : $i, X23 : $i]:
% 0.24/0.55         ~ (r2_hidden @ X23 @ (k4_xboole_0 @ X22 @ (k1_tarski @ X23)))),
% 0.24/0.55      inference('simplify', [status(thm)], ['23'])).
% 0.24/0.55  thf('25', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['22', '24'])).
% 0.24/0.55  thf('26', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.24/0.55          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['21', '25'])).
% 0.24/0.55  thf('27', plain, (![X18 : $i]: ((k1_xboole_0) != (k1_tarski @ X18))),
% 0.24/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.24/0.55  thf('28', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.24/0.55      inference('clc', [status(thm)], ['26', '27'])).
% 0.24/0.55  thf('29', plain,
% 0.24/0.55      (((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_A) != (sk_A))))
% 0.24/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.24/0.55      inference('demod', [status(thm)], ['20', '28'])).
% 0.24/0.55  thf('30', plain,
% 0.24/0.55      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.24/0.55         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.24/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.24/0.55  thf('31', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.24/0.55      inference('clc', [status(thm)], ['4', '8'])).
% 0.24/0.55  thf('32', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('33', plain,
% 0.24/0.55      (![X30 : $i, X32 : $i]: ((k2_mcart_1 @ (k4_tarski @ X30 @ X32)) = (X32))),
% 0.24/0.55      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.24/0.55  thf('34', plain, (((k2_mcart_1 @ sk_A) = (sk_C))),
% 0.24/0.55      inference('sup+', [status(thm)], ['32', '33'])).
% 0.24/0.55  thf('35', plain,
% 0.24/0.55      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.24/0.55      inference('split', [status(esa)], ['13'])).
% 0.24/0.55  thf('36', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.24/0.55      inference('sup+', [status(thm)], ['34', '35'])).
% 0.24/0.55  thf('37', plain, (((sk_A) = (k4_tarski @ sk_B_1 @ sk_C))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('38', plain,
% 0.24/0.55      ((((sk_A) = (k4_tarski @ sk_B_1 @ sk_A)))
% 0.24/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.24/0.55      inference('sup+', [status(thm)], ['36', '37'])).
% 0.24/0.55  thf('39', plain,
% 0.24/0.55      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.24/0.55         (((X33) = (k1_xboole_0))
% 0.24/0.55          | ~ (r2_hidden @ X34 @ X33)
% 0.24/0.55          | ((sk_B @ X33) != (k4_tarski @ X35 @ X34)))),
% 0.24/0.55      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.24/0.55  thf('40', plain,
% 0.24/0.55      ((![X0 : $i]:
% 0.24/0.55          (((sk_B @ X0) != (sk_A))
% 0.24/0.55           | ~ (r2_hidden @ sk_A @ X0)
% 0.24/0.55           | ((X0) = (k1_xboole_0))))
% 0.24/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['38', '39'])).
% 0.24/0.55  thf('41', plain,
% 0.24/0.55      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.24/0.55         | ((sk_B @ (k1_tarski @ sk_A)) != (sk_A))))
% 0.24/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['31', '40'])).
% 0.24/0.55  thf('42', plain, (![X0 : $i]: ((X0) = (sk_B @ (k1_tarski @ X0)))),
% 0.24/0.55      inference('clc', [status(thm)], ['26', '27'])).
% 0.24/0.55  thf('43', plain,
% 0.24/0.55      (((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_A) != (sk_A))))
% 0.24/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.24/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.24/0.55  thf('44', plain,
% 0.24/0.55      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.24/0.55         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.24/0.55      inference('simplify', [status(thm)], ['43'])).
% 0.24/0.55  thf('45', plain, (![X18 : $i]: ((k1_xboole_0) != (k1_tarski @ X18))),
% 0.24/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.24/0.55  thf('46', plain,
% 0.24/0.55      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.24/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.24/0.55  thf('47', plain, (~ (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.24/0.55      inference('simplify', [status(thm)], ['46'])).
% 0.24/0.55  thf('48', plain,
% 0.24/0.55      ((((sk_A) = (k1_mcart_1 @ sk_A))) | (((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.24/0.55      inference('split', [status(esa)], ['13'])).
% 0.24/0.55  thf('49', plain, ((((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.24/0.55      inference('sat_resolution*', [status(thm)], ['47', '48'])).
% 0.24/0.55  thf('50', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.24/0.55      inference('simpl_trail', [status(thm)], ['30', '49'])).
% 0.24/0.55  thf('51', plain, (![X18 : $i]: ((k1_xboole_0) != (k1_tarski @ X18))),
% 0.24/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.24/0.55  thf('52', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.24/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.24/0.55  thf('53', plain, ($false), inference('simplify', [status(thm)], ['52'])).
% 0.24/0.55  
% 0.24/0.55  % SZS output end Refutation
% 0.24/0.55  
% 0.40/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
