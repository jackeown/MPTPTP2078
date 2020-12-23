%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wMRBxjyR4v

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:36 EST 2020

% Result     : Theorem 9.64s
% Output     : Refutation 9.64s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 184 expanded)
%              Number of leaves         :   10 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  721 (2313 expanded)
%              Number of equality atoms :   63 ( 187 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t72_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
      <=> ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X9 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('6',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X9 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','12'])).

thf('14',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X6: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ( X10 = X9 )
      | ( X10 = X6 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('23',plain,(
    ! [X6: $i,X9: $i,X10: $i] :
      ( ( X10 = X6 )
      | ( X10 = X9 )
      | ~ ( r2_hidden @ X10 @ ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ( ( sk_D @ X2 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X1 )
      | ( ( sk_D @ X2 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( sk_D @ X1 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X2 ) ) )
      | ( ( sk_D @ X1 @ ( k2_tarski @ X0 @ X2 ) @ X1 )
        = X2 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X2 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k2_tarski @ X2 @ X0 ) ) )
      | ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['15'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('33',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X2 @ X1 )
        = ( k4_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','36'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('39',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('40',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('41',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('46',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','12','44','45'])).

thf('47',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['38','46'])).

thf('48',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
     != ( k2_tarski @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['37','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['50'])).

thf('53',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','12','44','45','52'])).

thf('54',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['51','53'])).

thf('55',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['49','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['14','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wMRBxjyR4v
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:28:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 9.64/9.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 9.64/9.87  % Solved by: fo/fo7.sh
% 9.64/9.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.64/9.87  % done 5558 iterations in 9.414s
% 9.64/9.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 9.64/9.87  % SZS output start Refutation
% 9.64/9.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.64/9.87  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 9.64/9.87  thf(sk_C_type, type, sk_C: $i).
% 9.64/9.87  thf(sk_B_type, type, sk_B: $i).
% 9.64/9.87  thf(sk_A_type, type, sk_A: $i).
% 9.64/9.87  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.64/9.87  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 9.64/9.87  thf(t72_zfmisc_1, conjecture,
% 9.64/9.87    (![A:$i,B:$i,C:$i]:
% 9.64/9.87     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 9.64/9.87       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 9.64/9.87  thf(zf_stmt_0, negated_conjecture,
% 9.64/9.87    (~( ![A:$i,B:$i,C:$i]:
% 9.64/9.87        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 9.64/9.87          ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ) )),
% 9.64/9.87    inference('cnf.neg', [status(esa)], [t72_zfmisc_1])).
% 9.64/9.87  thf('0', plain,
% 9.64/9.87      ((~ (r2_hidden @ sk_A @ sk_C)
% 9.64/9.87        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87            = (k2_tarski @ sk_A @ sk_B)))),
% 9.64/9.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.87  thf('1', plain,
% 9.64/9.87      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 9.64/9.87      inference('split', [status(esa)], ['0'])).
% 9.64/9.87  thf('2', plain,
% 9.64/9.87      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 9.64/9.87       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87          = (k2_tarski @ sk_A @ sk_B)))),
% 9.64/9.87      inference('split', [status(esa)], ['0'])).
% 9.64/9.87  thf('3', plain,
% 9.64/9.87      (((r2_hidden @ sk_B @ sk_C)
% 9.64/9.87        | (r2_hidden @ sk_A @ sk_C)
% 9.64/9.87        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87            != (k2_tarski @ sk_A @ sk_B)))),
% 9.64/9.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.87  thf('4', plain,
% 9.64/9.87      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 9.64/9.87      inference('split', [status(esa)], ['3'])).
% 9.64/9.87  thf(d2_tarski, axiom,
% 9.64/9.87    (![A:$i,B:$i,C:$i]:
% 9.64/9.87     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 9.64/9.87       ( ![D:$i]:
% 9.64/9.87         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 9.64/9.87  thf('5', plain,
% 9.64/9.87      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 9.64/9.87         (((X7) != (X9))
% 9.64/9.87          | (r2_hidden @ X7 @ X8)
% 9.64/9.87          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 9.64/9.87      inference('cnf', [status(esa)], [d2_tarski])).
% 9.64/9.87  thf('6', plain,
% 9.64/9.87      (![X6 : $i, X9 : $i]: (r2_hidden @ X9 @ (k2_tarski @ X9 @ X6))),
% 9.64/9.87      inference('simplify', [status(thm)], ['5'])).
% 9.64/9.87  thf('7', plain,
% 9.64/9.87      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87          = (k2_tarski @ sk_A @ sk_B)))
% 9.64/9.87         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87                = (k2_tarski @ sk_A @ sk_B))))),
% 9.64/9.87      inference('split', [status(esa)], ['0'])).
% 9.64/9.87  thf(d5_xboole_0, axiom,
% 9.64/9.87    (![A:$i,B:$i,C:$i]:
% 9.64/9.87     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 9.64/9.87       ( ![D:$i]:
% 9.64/9.87         ( ( r2_hidden @ D @ C ) <=>
% 9.64/9.87           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 9.64/9.87  thf('8', plain,
% 9.64/9.87      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 9.64/9.87         (~ (r2_hidden @ X4 @ X3)
% 9.64/9.87          | ~ (r2_hidden @ X4 @ X2)
% 9.64/9.87          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 9.64/9.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 9.64/9.87  thf('9', plain,
% 9.64/9.87      (![X1 : $i, X2 : $i, X4 : $i]:
% 9.64/9.87         (~ (r2_hidden @ X4 @ X2)
% 9.64/9.87          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 9.64/9.87      inference('simplify', [status(thm)], ['8'])).
% 9.64/9.87  thf('10', plain,
% 9.64/9.87      ((![X0 : $i]:
% 9.64/9.87          (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 9.64/9.87           | ~ (r2_hidden @ X0 @ sk_C)))
% 9.64/9.87         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87                = (k2_tarski @ sk_A @ sk_B))))),
% 9.64/9.87      inference('sup-', [status(thm)], ['7', '9'])).
% 9.64/9.87  thf('11', plain,
% 9.64/9.87      ((~ (r2_hidden @ sk_A @ sk_C))
% 9.64/9.87         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87                = (k2_tarski @ sk_A @ sk_B))))),
% 9.64/9.87      inference('sup-', [status(thm)], ['6', '10'])).
% 9.64/9.87  thf('12', plain,
% 9.64/9.87      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 9.64/9.87       ~
% 9.64/9.87       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87          = (k2_tarski @ sk_A @ sk_B)))),
% 9.64/9.87      inference('sup-', [status(thm)], ['4', '11'])).
% 9.64/9.87  thf('13', plain, (~ ((r2_hidden @ sk_A @ sk_C))),
% 9.64/9.87      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 9.64/9.87  thf('14', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 9.64/9.87      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 9.64/9.87  thf('15', plain,
% 9.64/9.87      (![X1 : $i, X2 : $i, X5 : $i]:
% 9.64/9.87         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 9.64/9.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 9.64/9.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 9.64/9.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 9.64/9.87  thf('16', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i]:
% 9.64/9.87         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 9.64/9.87          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 9.64/9.87      inference('eq_fact', [status(thm)], ['15'])).
% 9.64/9.87  thf('17', plain,
% 9.64/9.87      (![X1 : $i, X2 : $i, X5 : $i]:
% 9.64/9.87         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 9.64/9.87          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 9.64/9.87          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 9.64/9.87          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 9.64/9.87      inference('cnf', [status(esa)], [d5_xboole_0])).
% 9.64/9.87  thf('18', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i]:
% 9.64/9.87         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 9.64/9.87          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 9.64/9.87          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 9.64/9.87          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 9.64/9.87      inference('sup-', [status(thm)], ['16', '17'])).
% 9.64/9.87  thf('19', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i]:
% 9.64/9.87         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 9.64/9.87          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 9.64/9.87          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 9.64/9.87      inference('simplify', [status(thm)], ['18'])).
% 9.64/9.87  thf('20', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i]:
% 9.64/9.87         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 9.64/9.87          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 9.64/9.87      inference('eq_fact', [status(thm)], ['15'])).
% 9.64/9.87  thf('21', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i]:
% 9.64/9.87         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 9.64/9.87          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 9.64/9.87      inference('clc', [status(thm)], ['19', '20'])).
% 9.64/9.87  thf('22', plain,
% 9.64/9.87      (![X6 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 9.64/9.87         (~ (r2_hidden @ X10 @ X8)
% 9.64/9.87          | ((X10) = (X9))
% 9.64/9.87          | ((X10) = (X6))
% 9.64/9.87          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 9.64/9.87      inference('cnf', [status(esa)], [d2_tarski])).
% 9.64/9.87  thf('23', plain,
% 9.64/9.87      (![X6 : $i, X9 : $i, X10 : $i]:
% 9.64/9.87         (((X10) = (X6))
% 9.64/9.87          | ((X10) = (X9))
% 9.64/9.87          | ~ (r2_hidden @ X10 @ (k2_tarski @ X9 @ X6)))),
% 9.64/9.87      inference('simplify', [status(thm)], ['22'])).
% 9.64/9.87  thf('24', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.64/9.87         (((X2) = (k4_xboole_0 @ X2 @ (k2_tarski @ X1 @ X0)))
% 9.64/9.87          | ((sk_D @ X2 @ (k2_tarski @ X1 @ X0) @ X2) = (X1))
% 9.64/9.87          | ((sk_D @ X2 @ (k2_tarski @ X1 @ X0) @ X2) = (X0)))),
% 9.64/9.87      inference('sup-', [status(thm)], ['21', '23'])).
% 9.64/9.87  thf('25', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i]:
% 9.64/9.87         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 9.64/9.87          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 9.64/9.87      inference('eq_fact', [status(thm)], ['15'])).
% 9.64/9.87  thf('26', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.64/9.87         ((r2_hidden @ X0 @ X1)
% 9.64/9.87          | ((sk_D @ X1 @ (k2_tarski @ X0 @ X2) @ X1) = (X2))
% 9.64/9.87          | ((X1) = (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X2)))
% 9.64/9.87          | ((X1) = (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X2))))),
% 9.64/9.87      inference('sup+', [status(thm)], ['24', '25'])).
% 9.64/9.87  thf('27', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.64/9.87         (((X1) = (k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X2)))
% 9.64/9.87          | ((sk_D @ X1 @ (k2_tarski @ X0 @ X2) @ X1) = (X2))
% 9.64/9.87          | (r2_hidden @ X0 @ X1))),
% 9.64/9.87      inference('simplify', [status(thm)], ['26'])).
% 9.64/9.87  thf('28', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i]:
% 9.64/9.87         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 9.64/9.87          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 9.64/9.87      inference('eq_fact', [status(thm)], ['15'])).
% 9.64/9.87  thf('29', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.64/9.87         ((r2_hidden @ X0 @ X1)
% 9.64/9.87          | (r2_hidden @ X2 @ X1)
% 9.64/9.87          | ((X1) = (k4_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0)))
% 9.64/9.87          | ((X1) = (k4_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0))))),
% 9.64/9.87      inference('sup+', [status(thm)], ['27', '28'])).
% 9.64/9.87  thf('30', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.64/9.87         (((X1) = (k4_xboole_0 @ X1 @ (k2_tarski @ X2 @ X0)))
% 9.64/9.87          | (r2_hidden @ X2 @ X1)
% 9.64/9.87          | (r2_hidden @ X0 @ X1))),
% 9.64/9.87      inference('simplify', [status(thm)], ['29'])).
% 9.64/9.87  thf('31', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i]:
% 9.64/9.87         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 9.64/9.87          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 9.64/9.87      inference('eq_fact', [status(thm)], ['15'])).
% 9.64/9.87  thf('32', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i]:
% 9.64/9.87         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 9.64/9.87          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 9.64/9.87      inference('clc', [status(thm)], ['19', '20'])).
% 9.64/9.87  thf('33', plain,
% 9.64/9.87      (![X1 : $i, X2 : $i, X4 : $i]:
% 9.64/9.87         (~ (r2_hidden @ X4 @ X2)
% 9.64/9.87          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 9.64/9.87      inference('simplify', [status(thm)], ['8'])).
% 9.64/9.87  thf('34', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.64/9.87         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 9.64/9.87          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 9.64/9.87      inference('sup-', [status(thm)], ['32', '33'])).
% 9.64/9.87  thf('35', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i]:
% 9.64/9.87         (((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 9.64/9.87          | ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 9.64/9.87      inference('sup-', [status(thm)], ['31', '34'])).
% 9.64/9.87  thf('36', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i]:
% 9.64/9.87         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 9.64/9.87      inference('simplify', [status(thm)], ['35'])).
% 9.64/9.87  thf('37', plain,
% 9.64/9.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.64/9.87         (((k2_tarski @ X2 @ X1) = (k4_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0))
% 9.64/9.87          | (r2_hidden @ X1 @ X0)
% 9.64/9.87          | (r2_hidden @ X2 @ X0))),
% 9.64/9.87      inference('sup+', [status(thm)], ['30', '36'])).
% 9.64/9.87  thf('38', plain,
% 9.64/9.87      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87          != (k2_tarski @ sk_A @ sk_B)))
% 9.64/9.87         <= (~
% 9.64/9.87             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87                = (k2_tarski @ sk_A @ sk_B))))),
% 9.64/9.87      inference('split', [status(esa)], ['3'])).
% 9.64/9.87  thf('39', plain,
% 9.64/9.87      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 9.64/9.87      inference('split', [status(esa)], ['3'])).
% 9.64/9.87  thf('40', plain,
% 9.64/9.87      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 9.64/9.87         (((X7) != (X6))
% 9.64/9.87          | (r2_hidden @ X7 @ X8)
% 9.64/9.87          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 9.64/9.87      inference('cnf', [status(esa)], [d2_tarski])).
% 9.64/9.87  thf('41', plain,
% 9.64/9.87      (![X6 : $i, X9 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X9 @ X6))),
% 9.64/9.87      inference('simplify', [status(thm)], ['40'])).
% 9.64/9.87  thf('42', plain,
% 9.64/9.87      ((![X0 : $i]:
% 9.64/9.87          (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 9.64/9.87           | ~ (r2_hidden @ X0 @ sk_C)))
% 9.64/9.87         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87                = (k2_tarski @ sk_A @ sk_B))))),
% 9.64/9.87      inference('sup-', [status(thm)], ['7', '9'])).
% 9.64/9.87  thf('43', plain,
% 9.64/9.87      ((~ (r2_hidden @ sk_B @ sk_C))
% 9.64/9.87         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87                = (k2_tarski @ sk_A @ sk_B))))),
% 9.64/9.87      inference('sup-', [status(thm)], ['41', '42'])).
% 9.64/9.87  thf('44', plain,
% 9.64/9.87      (~ ((r2_hidden @ sk_B @ sk_C)) | 
% 9.64/9.87       ~
% 9.64/9.87       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87          = (k2_tarski @ sk_A @ sk_B)))),
% 9.64/9.87      inference('sup-', [status(thm)], ['39', '43'])).
% 9.64/9.87  thf('45', plain,
% 9.64/9.87      (~
% 9.64/9.87       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87          = (k2_tarski @ sk_A @ sk_B))) | 
% 9.64/9.87       ((r2_hidden @ sk_B @ sk_C)) | ((r2_hidden @ sk_A @ sk_C))),
% 9.64/9.87      inference('split', [status(esa)], ['3'])).
% 9.64/9.87  thf('46', plain,
% 9.64/9.87      (~
% 9.64/9.87       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87          = (k2_tarski @ sk_A @ sk_B)))),
% 9.64/9.87      inference('sat_resolution*', [status(thm)], ['2', '12', '44', '45'])).
% 9.64/9.87  thf('47', plain,
% 9.64/9.87      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87         != (k2_tarski @ sk_A @ sk_B))),
% 9.64/9.87      inference('simpl_trail', [status(thm)], ['38', '46'])).
% 9.64/9.87  thf('48', plain,
% 9.64/9.87      ((((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))
% 9.64/9.87        | (r2_hidden @ sk_A @ sk_C)
% 9.64/9.87        | (r2_hidden @ sk_B @ sk_C))),
% 9.64/9.87      inference('sup-', [status(thm)], ['37', '47'])).
% 9.64/9.87  thf('49', plain, (((r2_hidden @ sk_B @ sk_C) | (r2_hidden @ sk_A @ sk_C))),
% 9.64/9.87      inference('simplify', [status(thm)], ['48'])).
% 9.64/9.87  thf('50', plain,
% 9.64/9.87      ((~ (r2_hidden @ sk_B @ sk_C)
% 9.64/9.87        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87            = (k2_tarski @ sk_A @ sk_B)))),
% 9.64/9.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.64/9.87  thf('51', plain,
% 9.64/9.87      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 9.64/9.87      inference('split', [status(esa)], ['50'])).
% 9.64/9.87  thf('52', plain,
% 9.64/9.87      (~ ((r2_hidden @ sk_B @ sk_C)) | 
% 9.64/9.87       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 9.64/9.87          = (k2_tarski @ sk_A @ sk_B)))),
% 9.64/9.87      inference('split', [status(esa)], ['50'])).
% 9.64/9.87  thf('53', plain, (~ ((r2_hidden @ sk_B @ sk_C))),
% 9.64/9.87      inference('sat_resolution*', [status(thm)], ['2', '12', '44', '45', '52'])).
% 9.64/9.87  thf('54', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 9.64/9.87      inference('simpl_trail', [status(thm)], ['51', '53'])).
% 9.64/9.87  thf('55', plain, ((r2_hidden @ sk_A @ sk_C)),
% 9.64/9.87      inference('clc', [status(thm)], ['49', '54'])).
% 9.64/9.87  thf('56', plain, ($false), inference('demod', [status(thm)], ['14', '55'])).
% 9.64/9.87  
% 9.64/9.87  % SZS output end Refutation
% 9.64/9.87  
% 9.64/9.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
