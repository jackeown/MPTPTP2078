%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E83FPTmaWR

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:58 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 123 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  571 (1273 expanded)
%              Number of equality atoms :   72 ( 170 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(t19_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( ( ( k2_mcart_1 @ A )
            = D )
          | ( ( k2_mcart_1 @ A )
            = E ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( ( ( k2_mcart_1 @ A )
              = D )
            | ( ( k2_mcart_1 @ A )
              = E ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_mcart_1])).

thf('0',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_2 )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_2 )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_2 )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_2 )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ ( k2_tarski @ X21 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C_2 ) @ ( k2_tarski @ sk_D_1 @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X25 ) @ X27 )
      | ~ ( r2_hidden @ X25 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('16',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_D_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( r2_hidden @ X20 @ X19 )
      | ( X19
        = ( k4_xboole_0 @ X19 @ ( k2_tarski @ X18 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_E @ X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_E @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_D_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('23',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( X13 = X10 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('24',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( sk_E
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('27',plain,
    ( ( sk_E
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_D_1
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_E )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( ( sk_E != sk_E )
      | ( sk_D_1
        = ( k2_mcart_1 @ sk_A ) ) )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ sk_A ) )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('33',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( ( ( k2_mcart_1 @ sk_A )
       != sk_E )
      & ( ( k2_mcart_1 @ sk_A )
       != sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_E )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D_1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(split,[status(esa)],['28'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','12'])).

thf('37',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C_2 ) @ ( k2_tarski @ sk_D_1 @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X25 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('39',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_C_2 @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('44',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( sk_C_2
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('46',plain,
    ( ( sk_C_2
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_B
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_2 )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('48',plain,
    ( ( ( sk_C_2 != sk_C_2 )
      | ( sk_B
        = ( k1_mcart_1 @ sk_A ) ) )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C_2 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B
      = ( k1_mcart_1 @ sk_A ) )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C_2 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('51',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k1_mcart_1 @ sk_A )
       != sk_C_2 )
      & ( ( k1_mcart_1 @ sk_A )
       != sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C_2 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','34','35','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.E83FPTmaWR
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:54:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 347 iterations in 0.188s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.63  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.63  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.63  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.45/0.63  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.45/0.63  thf(t19_mcart_1, conjecture,
% 0.45/0.63    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.63     ( ( r2_hidden @
% 0.45/0.63         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) =>
% 0.45/0.63       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.45/0.63         ( ( ( k2_mcart_1 @ A ) = ( D ) ) | ( ( k2_mcart_1 @ A ) = ( E ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.63        ( ( r2_hidden @
% 0.45/0.63            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) =>
% 0.45/0.63          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.45/0.63            ( ( ( k2_mcart_1 @ A ) = ( D ) ) | ( ( k2_mcart_1 @ A ) = ( E ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t19_mcart_1])).
% 0.45/0.63  thf('0', plain,
% 0.45/0.63      ((((k1_mcart_1 @ sk_A) != (sk_C_2)) | ((k2_mcart_1 @ sk_A) != (sk_E)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (~ (((k1_mcart_1 @ sk_A) = (sk_C_2))) | 
% 0.45/0.63       ~ (((k2_mcart_1 @ sk_A) = (sk_E)))),
% 0.45/0.63      inference('split', [status(esa)], ['0'])).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.45/0.63       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.45/0.63      inference('split', [status(esa)], ['2'])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      ((((k1_mcart_1 @ sk_A) != (sk_C_2)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (~ (((k1_mcart_1 @ sk_A) = (sk_C_2))) | 
% 0.45/0.63       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.45/0.63      inference('split', [status(esa)], ['4'])).
% 0.45/0.63  thf(t69_enumset1, axiom,
% 0.45/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.63  thf('6', plain, (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.45/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.63  thf(d3_tarski, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      (![X1 : $i, X3 : $i]:
% 0.45/0.63         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.63  thf('8', plain,
% 0.45/0.63      (![X1 : $i, X3 : $i]:
% 0.45/0.63         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.45/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.63  thf('9', plain,
% 0.45/0.63      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.63  thf('10', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.45/0.63      inference('simplify', [status(thm)], ['9'])).
% 0.45/0.63  thf(t38_zfmisc_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.45/0.63       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.45/0.63         ((r2_hidden @ X21 @ X22)
% 0.45/0.63          | ~ (r1_tarski @ (k2_tarski @ X21 @ X23) @ X22))),
% 0.45/0.63      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.63  thf('13', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['6', '12'])).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      ((r2_hidden @ sk_A @ 
% 0.45/0.63        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C_2) @ 
% 0.45/0.63         (k2_tarski @ sk_D_1 @ sk_E)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(t10_mcart_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.45/0.63       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.45/0.63         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.45/0.63  thf('15', plain,
% 0.45/0.63      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.63         ((r2_hidden @ (k2_mcart_1 @ X25) @ X27)
% 0.45/0.63          | ~ (r2_hidden @ X25 @ (k2_zfmisc_1 @ X26 @ X27)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.45/0.63  thf('16', plain,
% 0.45/0.63      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_D_1 @ sk_E))),
% 0.45/0.63      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.63  thf(t144_zfmisc_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.45/0.63          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.45/0.63  thf('17', plain,
% 0.45/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.63         ((r2_hidden @ X18 @ X19)
% 0.45/0.63          | (r2_hidden @ X20 @ X19)
% 0.45/0.63          | ((X19) = (k4_xboole_0 @ X19 @ (k2_tarski @ X18 @ X20))))),
% 0.45/0.63      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 0.45/0.63  thf(d5_xboole_0, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.45/0.63       ( ![D:$i]:
% 0.45/0.63         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.63           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.45/0.63  thf('18', plain,
% 0.45/0.63      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X8 @ X7)
% 0.45/0.63          | ~ (r2_hidden @ X8 @ X6)
% 0.45/0.63          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X8 @ X6)
% 0.45/0.63          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['18'])).
% 0.45/0.63  thf('20', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X3 @ X0)
% 0.45/0.63          | (r2_hidden @ X1 @ X0)
% 0.45/0.63          | (r2_hidden @ X2 @ X0)
% 0.45/0.63          | ~ (r2_hidden @ X3 @ (k2_tarski @ X2 @ X1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['17', '19'])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((r2_hidden @ sk_D_1 @ X0)
% 0.45/0.63          | (r2_hidden @ sk_E @ X0)
% 0.45/0.63          | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['16', '20'])).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      (((r2_hidden @ sk_E @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 0.45/0.63        | (r2_hidden @ sk_D_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['13', '21'])).
% 0.45/0.63  thf(d1_tarski, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X13 @ X12)
% 0.45/0.63          | ((X13) = (X10))
% 0.45/0.63          | ((X12) != (k1_tarski @ X10)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      (![X10 : $i, X13 : $i]:
% 0.45/0.63         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      (((r2_hidden @ sk_D_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 0.45/0.63        | ((sk_E) = (k2_mcart_1 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['22', '24'])).
% 0.45/0.63  thf('26', plain,
% 0.45/0.63      (![X10 : $i, X13 : $i]:
% 0.45/0.63         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      ((((sk_E) = (k2_mcart_1 @ sk_A)) | ((sk_D_1) = (k2_mcart_1 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_E)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('29', plain,
% 0.45/0.63      ((((k2_mcart_1 @ sk_A) != (sk_E)))
% 0.45/0.63         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))))),
% 0.45/0.63      inference('split', [status(esa)], ['28'])).
% 0.45/0.63  thf('30', plain,
% 0.45/0.63      (((((sk_E) != (sk_E)) | ((sk_D_1) = (k2_mcart_1 @ sk_A))))
% 0.45/0.63         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['27', '29'])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      ((((sk_D_1) = (k2_mcart_1 @ sk_A)))
% 0.45/0.63         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))))),
% 0.45/0.63      inference('simplify', [status(thm)], ['30'])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 0.45/0.63         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.45/0.63      inference('split', [status(esa)], ['2'])).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      ((((sk_D_1) != (sk_D_1)))
% 0.45/0.63         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))) & 
% 0.45/0.63             ~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      ((((k2_mcart_1 @ sk_A) = (sk_E))) | (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['33'])).
% 0.45/0.63  thf('35', plain,
% 0.45/0.63      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_E)))),
% 0.45/0.63      inference('split', [status(esa)], ['28'])).
% 0.45/0.63  thf('36', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.63      inference('sup+', [status(thm)], ['6', '12'])).
% 0.45/0.63  thf('37', plain,
% 0.45/0.63      ((r2_hidden @ sk_A @ 
% 0.45/0.63        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C_2) @ 
% 0.45/0.63         (k2_tarski @ sk_D_1 @ sk_E)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('38', plain,
% 0.45/0.63      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.63         ((r2_hidden @ (k1_mcart_1 @ X25) @ X26)
% 0.45/0.63          | ~ (r2_hidden @ X25 @ (k2_zfmisc_1 @ X26 @ X27)))),
% 0.45/0.63      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.45/0.63  thf('39', plain,
% 0.45/0.63      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C_2))),
% 0.45/0.63      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.63  thf('40', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X3 @ X0)
% 0.45/0.63          | (r2_hidden @ X1 @ X0)
% 0.45/0.63          | (r2_hidden @ X2 @ X0)
% 0.45/0.63          | ~ (r2_hidden @ X3 @ (k2_tarski @ X2 @ X1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['17', '19'])).
% 0.45/0.63  thf('41', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         ((r2_hidden @ sk_B @ X0)
% 0.45/0.63          | (r2_hidden @ sk_C_2 @ X0)
% 0.45/0.63          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.45/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.63  thf('42', plain,
% 0.45/0.63      (((r2_hidden @ sk_C_2 @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.45/0.63        | (r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['36', '41'])).
% 0.45/0.63  thf('43', plain,
% 0.45/0.63      (![X10 : $i, X13 : $i]:
% 0.45/0.63         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.63  thf('44', plain,
% 0.45/0.63      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.45/0.63        | ((sk_C_2) = (k1_mcart_1 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.63  thf('45', plain,
% 0.45/0.63      (![X10 : $i, X13 : $i]:
% 0.45/0.63         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.63  thf('46', plain,
% 0.45/0.63      ((((sk_C_2) = (k1_mcart_1 @ sk_A)) | ((sk_B) = (k1_mcart_1 @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.63  thf('47', plain,
% 0.45/0.63      ((((k1_mcart_1 @ sk_A) != (sk_C_2)))
% 0.45/0.63         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C_2))))),
% 0.45/0.63      inference('split', [status(esa)], ['4'])).
% 0.45/0.63  thf('48', plain,
% 0.45/0.63      (((((sk_C_2) != (sk_C_2)) | ((sk_B) = (k1_mcart_1 @ sk_A))))
% 0.45/0.63         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C_2))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.63  thf('49', plain,
% 0.45/0.63      ((((sk_B) = (k1_mcart_1 @ sk_A)))
% 0.45/0.63         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C_2))))),
% 0.45/0.63      inference('simplify', [status(thm)], ['48'])).
% 0.45/0.63  thf('50', plain,
% 0.45/0.63      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.45/0.63         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.45/0.63      inference('split', [status(esa)], ['2'])).
% 0.45/0.63  thf('51', plain,
% 0.45/0.63      ((((sk_B) != (sk_B)))
% 0.45/0.63         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C_2))) & 
% 0.45/0.63             ~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.45/0.63      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.63  thf('52', plain,
% 0.45/0.63      ((((k1_mcart_1 @ sk_A) = (sk_B))) | (((k1_mcart_1 @ sk_A) = (sk_C_2)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['51'])).
% 0.45/0.63  thf('53', plain, ($false),
% 0.45/0.63      inference('sat_resolution*', [status(thm)],
% 0.45/0.63                ['1', '3', '5', '34', '35', '52'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.45/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
