%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5Ixx3fnABD

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:20 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 453 expanded)
%              Number of leaves         :   21 ( 141 expanded)
%              Depth                    :   23
%              Number of atoms          :  582 (3558 expanded)
%              Number of equality atoms :   89 ( 569 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('1',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( r2_hidden @ X58 @ X57 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ X58 @ X56 ) @ X58 ) @ X56 )
      | ( X57
       != ( k2_relat_1 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('2',plain,(
    ! [X56: $i,X58: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ X58 @ X56 ) @ X58 ) @ X56 )
      | ~ ( r2_hidden @ X58 @ ( k2_relat_1 @ X56 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_4 @ ( sk_B @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_B @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X22: $i] :
      ( ( X22
        = ( k1_tarski @ X18 ) )
      | ( ( sk_C_1 @ X22 @ X18 )
        = X18 )
      | ( r2_hidden @ ( sk_C_1 @ X22 @ X18 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('7',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C_1 @ X0 @ X1 )
        = X1 )
      | ( X0
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X1 ) )
      | ( ( sk_C_1 @ k1_xboole_0 @ X1 )
        = X1 ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('11',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X38 ) @ X39 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X1 ) @ X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X1 )
        = X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','12'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('14',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('15',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('16',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X18: $i,X22: $i] :
      ( ( X22
        = ( k1_tarski @ X18 ) )
      | ( ( sk_C_1 @ X22 @ X18 )
        = X18 )
      | ( r2_hidden @ ( sk_C_1 @ X22 @ X18 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = X0 )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = X0 )
      | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('26',plain,
    ( ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X18: $i,X22: $i] :
      ( ( X22
        = ( k1_tarski @ X18 ) )
      | ( ( sk_C_1 @ X22 @ X18 )
       != X18 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X22 @ X18 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('28',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['25'])).

thf('30',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('31',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( k1_xboole_0
      = ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('35',plain,(
    ( k1_zfmisc_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['23','36'])).

thf('38',plain,(
    ! [X18: $i,X22: $i] :
      ( ( X22
        = ( k1_tarski @ X18 ) )
      | ( ( sk_C_1 @ X22 @ X18 )
       != X18 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X22 @ X18 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
       != X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['23','36'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 != X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','44'])).

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

thf('46',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('49',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( r2_hidden @ X51 @ X50 )
      | ( r2_hidden @ ( k4_tarski @ X51 @ ( sk_D_2 @ X51 @ X49 ) ) @ X49 )
      | ( X50
       != ( k1_relat_1 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('50',plain,(
    ! [X49: $i,X51: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X51 @ ( sk_D_2 @ X51 @ X49 ) ) @ X49 )
      | ~ ( r2_hidden @ X51 @ ( k1_relat_1 @ X49 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_2 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('53',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['46'])).

thf('58',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['47','58'])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5Ixx3fnABD
% 0.13/0.36  % Computer   : n022.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 15:08:11 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.69/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.88  % Solved by: fo/fo7.sh
% 0.69/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.88  % done 904 iterations in 0.397s
% 0.69/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.88  % SZS output start Refutation
% 0.69/0.88  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.69/0.88  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.69/0.88  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i).
% 0.69/0.88  thf(sk_B_type, type, sk_B: $i > $i).
% 0.69/0.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.69/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.88  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.69/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.88  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.69/0.88  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.69/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.88  thf(t7_xboole_0, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.69/0.88          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.69/0.88  thf('0', plain,
% 0.69/0.88      (![X11 : $i]:
% 0.69/0.88         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.69/0.88      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.69/0.88  thf(d5_relat_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.69/0.88       ( ![C:$i]:
% 0.69/0.88         ( ( r2_hidden @ C @ B ) <=>
% 0.69/0.88           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.69/0.88  thf('1', plain,
% 0.69/0.88      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.69/0.88         (~ (r2_hidden @ X58 @ X57)
% 0.69/0.88          | (r2_hidden @ (k4_tarski @ (sk_D_4 @ X58 @ X56) @ X58) @ X56)
% 0.69/0.88          | ((X57) != (k2_relat_1 @ X56)))),
% 0.69/0.88      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.69/0.88  thf('2', plain,
% 0.69/0.88      (![X56 : $i, X58 : $i]:
% 0.69/0.88         ((r2_hidden @ (k4_tarski @ (sk_D_4 @ X58 @ X56) @ X58) @ X56)
% 0.69/0.88          | ~ (r2_hidden @ X58 @ (k2_relat_1 @ X56)))),
% 0.69/0.88      inference('simplify', [status(thm)], ['1'])).
% 0.69/0.88  thf('3', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.69/0.88          | (r2_hidden @ 
% 0.69/0.88             (k4_tarski @ (sk_D_4 @ (sk_B @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.69/0.88              (sk_B @ (k2_relat_1 @ X0))) @ 
% 0.69/0.88             X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['0', '2'])).
% 0.69/0.88  thf(t1_boole, axiom,
% 0.69/0.88    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.69/0.88  thf('4', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.69/0.88      inference('cnf', [status(esa)], [t1_boole])).
% 0.69/0.88  thf(d1_tarski, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.69/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.69/0.88  thf('5', plain,
% 0.69/0.88      (![X18 : $i, X22 : $i]:
% 0.69/0.88         (((X22) = (k1_tarski @ X18))
% 0.69/0.88          | ((sk_C_1 @ X22 @ X18) = (X18))
% 0.69/0.88          | (r2_hidden @ (sk_C_1 @ X22 @ X18) @ X22))),
% 0.69/0.88      inference('cnf', [status(esa)], [d1_tarski])).
% 0.69/0.88  thf(d3_xboole_0, axiom,
% 0.69/0.88    (![A:$i,B:$i,C:$i]:
% 0.69/0.88     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.69/0.88       ( ![D:$i]:
% 0.69/0.88         ( ( r2_hidden @ D @ C ) <=>
% 0.69/0.88           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.69/0.88  thf('6', plain,
% 0.69/0.88      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.69/0.88         (~ (r2_hidden @ X2 @ X3)
% 0.69/0.88          | (r2_hidden @ X2 @ X4)
% 0.69/0.88          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.69/0.88      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.69/0.88  thf('7', plain,
% 0.69/0.88      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.69/0.88         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.69/0.88      inference('simplify', [status(thm)], ['6'])).
% 0.69/0.88  thf('8', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.88         (((sk_C_1 @ X0 @ X1) = (X1))
% 0.69/0.88          | ((X0) = (k1_tarski @ X1))
% 0.69/0.88          | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['5', '7'])).
% 0.69/0.88  thf('9', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X1) @ X0)
% 0.69/0.88          | ((k1_xboole_0) = (k1_tarski @ X1))
% 0.69/0.88          | ((sk_C_1 @ k1_xboole_0 @ X1) = (X1)))),
% 0.69/0.88      inference('sup+', [status(thm)], ['4', '8'])).
% 0.69/0.88  thf('10', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.69/0.88      inference('cnf', [status(esa)], [t1_boole])).
% 0.69/0.88  thf(t49_zfmisc_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.69/0.88  thf('11', plain,
% 0.69/0.88      (![X38 : $i, X39 : $i]:
% 0.69/0.88         ((k2_xboole_0 @ (k1_tarski @ X38) @ X39) != (k1_xboole_0))),
% 0.69/0.88      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.69/0.88  thf('12', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['10', '11'])).
% 0.69/0.88  thf('13', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X1) @ X0)
% 0.69/0.88          | ((sk_C_1 @ k1_xboole_0 @ X1) = (X1)))),
% 0.69/0.88      inference('simplify_reflect-', [status(thm)], ['9', '12'])).
% 0.69/0.88  thf(t1_zfmisc_1, axiom,
% 0.69/0.88    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.69/0.88  thf('14', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.69/0.88      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.69/0.88  thf('15', plain,
% 0.69/0.88      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.69/0.88         (~ (r2_hidden @ X21 @ X20)
% 0.69/0.88          | ((X21) = (X18))
% 0.69/0.88          | ((X20) != (k1_tarski @ X18)))),
% 0.69/0.88      inference('cnf', [status(esa)], [d1_tarski])).
% 0.69/0.88  thf('16', plain,
% 0.69/0.88      (![X18 : $i, X21 : $i]:
% 0.69/0.88         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.69/0.88      inference('simplify', [status(thm)], ['15'])).
% 0.69/0.88  thf('17', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.69/0.88          | ((X0) = (k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['14', '16'])).
% 0.69/0.88  thf('18', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((sk_C_1 @ k1_xboole_0 @ X0) = (X0))
% 0.69/0.88          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['13', '17'])).
% 0.69/0.88  thf('19', plain,
% 0.69/0.88      (![X18 : $i, X22 : $i]:
% 0.69/0.88         (((X22) = (k1_tarski @ X18))
% 0.69/0.88          | ((sk_C_1 @ X22 @ X18) = (X18))
% 0.69/0.88          | (r2_hidden @ (sk_C_1 @ X22 @ X18) @ X22))),
% 0.69/0.88      inference('cnf', [status(esa)], [d1_tarski])).
% 0.69/0.88  thf('20', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.69/0.88          | ((sk_C_1 @ k1_xboole_0 @ X0) = (X0))
% 0.69/0.88          | ((sk_C_1 @ k1_xboole_0 @ X0) = (X0))
% 0.69/0.88          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 0.69/0.88      inference('sup+', [status(thm)], ['18', '19'])).
% 0.69/0.88  thf('21', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k1_xboole_0) = (k1_tarski @ X0))
% 0.69/0.88          | ((sk_C_1 @ k1_xboole_0 @ X0) = (X0))
% 0.69/0.88          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['20'])).
% 0.69/0.88  thf('22', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['10', '11'])).
% 0.69/0.88  thf('23', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((sk_C_1 @ k1_xboole_0 @ X0) = (X0))
% 0.69/0.88          | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 0.69/0.88      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.69/0.88  thf('24', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((sk_C_1 @ k1_xboole_0 @ X0) = (X0))
% 0.69/0.88          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['13', '17'])).
% 0.69/0.88  thf('25', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((X0) != (k1_xboole_0))
% 0.69/0.88          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.69/0.88      inference('eq_fact', [status(thm)], ['24'])).
% 0.69/0.88  thf('26', plain, (((sk_C_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['25'])).
% 0.69/0.88  thf('27', plain,
% 0.69/0.88      (![X18 : $i, X22 : $i]:
% 0.69/0.88         (((X22) = (k1_tarski @ X18))
% 0.69/0.88          | ((sk_C_1 @ X22 @ X18) != (X18))
% 0.69/0.88          | ~ (r2_hidden @ (sk_C_1 @ X22 @ X18) @ X22))),
% 0.69/0.88      inference('cnf', [status(esa)], [d1_tarski])).
% 0.69/0.88  thf('28', plain,
% 0.69/0.88      ((~ (r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.69/0.88        | ((sk_C_1 @ k1_xboole_0 @ k1_xboole_0) != (k1_xboole_0))
% 0.69/0.88        | ((k1_xboole_0) = (k1_tarski @ k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['26', '27'])).
% 0.69/0.88  thf('29', plain, (((sk_C_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['25'])).
% 0.69/0.88  thf('30', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.69/0.88      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.69/0.88  thf('31', plain,
% 0.69/0.88      ((~ (r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.69/0.88        | ((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.88        | ((k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.69/0.88  thf('32', plain,
% 0.69/0.88      ((((k1_xboole_0) = (k1_zfmisc_1 @ k1_xboole_0))
% 0.69/0.88        | ~ (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['31'])).
% 0.69/0.88  thf('33', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.69/0.88      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.69/0.88  thf('34', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['10', '11'])).
% 0.69/0.88  thf('35', plain, (((k1_zfmisc_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['33', '34'])).
% 0.69/0.88  thf('36', plain, (~ (r2_hidden @ k1_xboole_0 @ k1_xboole_0)),
% 0.69/0.88      inference('simplify_reflect-', [status(thm)], ['32', '35'])).
% 0.69/0.88  thf('37', plain, (![X0 : $i]: ((sk_C_1 @ k1_xboole_0 @ X0) = (X0))),
% 0.69/0.88      inference('clc', [status(thm)], ['23', '36'])).
% 0.69/0.88  thf('38', plain,
% 0.69/0.88      (![X18 : $i, X22 : $i]:
% 0.69/0.88         (((X22) = (k1_tarski @ X18))
% 0.69/0.88          | ((sk_C_1 @ X22 @ X18) != (X18))
% 0.69/0.88          | ~ (r2_hidden @ (sk_C_1 @ X22 @ X18) @ X22))),
% 0.69/0.88      inference('cnf', [status(esa)], [d1_tarski])).
% 0.69/0.88  thf('39', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.69/0.88          | ((sk_C_1 @ k1_xboole_0 @ X0) != (X0))
% 0.69/0.88          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['37', '38'])).
% 0.69/0.88  thf('40', plain, (![X0 : $i]: ((sk_C_1 @ k1_xboole_0 @ X0) = (X0))),
% 0.69/0.88      inference('clc', [status(thm)], ['23', '36'])).
% 0.69/0.88  thf('41', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.69/0.88          | ((X0) != (X0))
% 0.69/0.88          | ((k1_xboole_0) = (k1_tarski @ X0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['39', '40'])).
% 0.69/0.88  thf('42', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k1_xboole_0) = (k1_tarski @ X0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['41'])).
% 0.69/0.88  thf('43', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['10', '11'])).
% 0.69/0.88  thf('44', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.69/0.88      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.69/0.88  thf('45', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['3', '44'])).
% 0.69/0.88  thf(t60_relat_1, conjecture,
% 0.69/0.88    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.69/0.88     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.69/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.88    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.69/0.88        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.69/0.88    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.69/0.88  thf('46', plain,
% 0.69/0.88      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.69/0.88        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('47', plain,
% 0.69/0.88      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.69/0.88         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.69/0.88      inference('split', [status(esa)], ['46'])).
% 0.69/0.88  thf('48', plain,
% 0.69/0.88      (![X11 : $i]:
% 0.69/0.88         (((X11) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X11) @ X11))),
% 0.69/0.88      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.69/0.88  thf(d4_relat_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.69/0.88       ( ![C:$i]:
% 0.69/0.88         ( ( r2_hidden @ C @ B ) <=>
% 0.69/0.88           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.69/0.88  thf('49', plain,
% 0.69/0.88      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.69/0.88         (~ (r2_hidden @ X51 @ X50)
% 0.69/0.88          | (r2_hidden @ (k4_tarski @ X51 @ (sk_D_2 @ X51 @ X49)) @ X49)
% 0.69/0.88          | ((X50) != (k1_relat_1 @ X49)))),
% 0.69/0.88      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.69/0.88  thf('50', plain,
% 0.69/0.88      (![X49 : $i, X51 : $i]:
% 0.69/0.88         ((r2_hidden @ (k4_tarski @ X51 @ (sk_D_2 @ X51 @ X49)) @ X49)
% 0.69/0.88          | ~ (r2_hidden @ X51 @ (k1_relat_1 @ X49)))),
% 0.69/0.88      inference('simplify', [status(thm)], ['49'])).
% 0.69/0.88  thf('51', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.69/0.88          | (r2_hidden @ 
% 0.69/0.88             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 0.69/0.88              (sk_D_2 @ (sk_B @ (k1_relat_1 @ X0)) @ X0)) @ 
% 0.69/0.88             X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['48', '50'])).
% 0.69/0.88  thf('52', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.69/0.88      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.69/0.88  thf('53', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['51', '52'])).
% 0.69/0.88  thf('54', plain,
% 0.69/0.88      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.69/0.88         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.69/0.88      inference('split', [status(esa)], ['46'])).
% 0.69/0.88  thf('55', plain,
% 0.69/0.88      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.69/0.88         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['53', '54'])).
% 0.69/0.88  thf('56', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.69/0.88      inference('simplify', [status(thm)], ['55'])).
% 0.69/0.88  thf('57', plain,
% 0.69/0.88      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.69/0.88       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.69/0.88      inference('split', [status(esa)], ['46'])).
% 0.69/0.88  thf('58', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.69/0.88      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 0.69/0.88  thf('59', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.69/0.88      inference('simpl_trail', [status(thm)], ['47', '58'])).
% 0.69/0.88  thf('60', plain, ($false),
% 0.69/0.88      inference('simplify_reflect-', [status(thm)], ['45', '59'])).
% 0.69/0.88  
% 0.69/0.88  % SZS output end Refutation
% 0.69/0.88  
% 0.72/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
