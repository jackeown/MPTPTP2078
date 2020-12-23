%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eOKTGjvMki

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:42 EST 2020

% Result     : Theorem 3.13s
% Output     : Refutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :   64 (  95 expanded)
%              Number of leaves         :   17 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  544 ( 886 expanded)
%              Number of equality atoms :   61 ( 105 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X25 @ X26 ) @ X25 )
      | ( r2_hidden @ ( sk_C_2 @ X25 @ X26 ) @ X27 )
      | ~ ( r2_hidden @ X27 @ X26 )
      | ( X25
        = ( k1_setfam_1 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X25 @ X26 ) @ X25 )
      | ( r2_hidden @ ( sk_D @ X25 @ X26 ) @ X26 )
      | ( X25
        = ( k1_setfam_1 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_D @ X0 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X25 @ X26 ) @ X25 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X25 @ X26 ) @ ( sk_D @ X25 @ X26 ) )
      | ( X25
        = ( k1_setfam_1 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['3'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('16',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('20',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['18','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ ( k1_tarski @ X20 ) )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('23',plain,(
    ! [X20: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X20 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( ( sk_C @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ k1_xboole_0 )
       != sk_A )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( ( sk_C @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ~ ( r2_hidden @ X21 @ ( k4_xboole_0 @ X22 @ ( k1_tarski @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21 != X23 )
      | ~ ( r2_hidden @ X21 @ ( k4_xboole_0 @ X22 @ ( k1_tarski @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('43',plain,(
    ! [X22: $i,X23: $i] :
      ~ ( r2_hidden @ X23 @ ( k4_xboole_0 @ X22 @ ( k1_tarski @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    $false ),
    inference('sup-',[status(thm)],['20','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eOKTGjvMki
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:43:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.13/3.35  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.13/3.35  % Solved by: fo/fo7.sh
% 3.13/3.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.13/3.35  % done 1750 iterations in 2.889s
% 3.13/3.35  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.13/3.35  % SZS output start Refutation
% 3.13/3.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.13/3.35  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 3.13/3.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.13/3.35  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.13/3.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.13/3.35  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.13/3.35  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.13/3.35  thf(sk_A_type, type, sk_A: $i).
% 3.13/3.35  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 3.13/3.35  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 3.13/3.35  thf(d1_tarski, axiom,
% 3.13/3.35    (![A:$i,B:$i]:
% 3.13/3.35     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 3.13/3.35       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 3.13/3.35  thf('0', plain,
% 3.13/3.35      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.13/3.35         (((X8) != (X7)) | (r2_hidden @ X8 @ X9) | ((X9) != (k1_tarski @ X7)))),
% 3.13/3.35      inference('cnf', [status(esa)], [d1_tarski])).
% 3.13/3.35  thf('1', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 3.13/3.35      inference('simplify', [status(thm)], ['0'])).
% 3.13/3.35  thf(d1_setfam_1, axiom,
% 3.13/3.35    (![A:$i,B:$i]:
% 3.13/3.35     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 3.13/3.35         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 3.13/3.35       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 3.13/3.35         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 3.13/3.35           ( ![C:$i]:
% 3.13/3.35             ( ( r2_hidden @ C @ B ) <=>
% 3.13/3.35               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 3.13/3.35  thf('2', plain,
% 3.13/3.35      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.13/3.35         ((r2_hidden @ (sk_C_2 @ X25 @ X26) @ X25)
% 3.13/3.35          | (r2_hidden @ (sk_C_2 @ X25 @ X26) @ X27)
% 3.13/3.35          | ~ (r2_hidden @ X27 @ X26)
% 3.13/3.35          | ((X25) = (k1_setfam_1 @ X26))
% 3.13/3.35          | ((X26) = (k1_xboole_0)))),
% 3.13/3.35      inference('cnf', [status(esa)], [d1_setfam_1])).
% 3.13/3.35  thf('3', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         (((k1_tarski @ X0) = (k1_xboole_0))
% 3.13/3.35          | ((X1) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 3.13/3.35          | (r2_hidden @ (sk_C_2 @ X1 @ (k1_tarski @ X0)) @ X0)
% 3.13/3.35          | (r2_hidden @ (sk_C_2 @ X1 @ (k1_tarski @ X0)) @ X1))),
% 3.13/3.35      inference('sup-', [status(thm)], ['1', '2'])).
% 3.13/3.35  thf('4', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         ((r2_hidden @ (sk_C_2 @ X0 @ (k1_tarski @ X0)) @ X0)
% 3.13/3.35          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 3.13/3.35          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 3.13/3.35      inference('eq_fact', [status(thm)], ['3'])).
% 3.13/3.35  thf('5', plain,
% 3.13/3.35      (![X25 : $i, X26 : $i]:
% 3.13/3.35         (~ (r2_hidden @ (sk_C_2 @ X25 @ X26) @ X25)
% 3.13/3.35          | (r2_hidden @ (sk_D @ X25 @ X26) @ X26)
% 3.13/3.35          | ((X25) = (k1_setfam_1 @ X26))
% 3.13/3.35          | ((X26) = (k1_xboole_0)))),
% 3.13/3.35      inference('cnf', [status(esa)], [d1_setfam_1])).
% 3.13/3.35  thf('6', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (((k1_tarski @ X0) = (k1_xboole_0))
% 3.13/3.35          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 3.13/3.35          | ((k1_tarski @ X0) = (k1_xboole_0))
% 3.13/3.35          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 3.13/3.35          | (r2_hidden @ (sk_D @ X0 @ (k1_tarski @ X0)) @ (k1_tarski @ X0)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['4', '5'])).
% 3.13/3.35  thf('7', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         ((r2_hidden @ (sk_D @ X0 @ (k1_tarski @ X0)) @ (k1_tarski @ X0))
% 3.13/3.35          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 3.13/3.35          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 3.13/3.35      inference('simplify', [status(thm)], ['6'])).
% 3.13/3.35  thf('8', plain,
% 3.13/3.35      (![X7 : $i, X9 : $i, X10 : $i]:
% 3.13/3.35         (~ (r2_hidden @ X10 @ X9)
% 3.13/3.35          | ((X10) = (X7))
% 3.13/3.35          | ((X9) != (k1_tarski @ X7)))),
% 3.13/3.35      inference('cnf', [status(esa)], [d1_tarski])).
% 3.13/3.35  thf('9', plain,
% 3.13/3.35      (![X7 : $i, X10 : $i]:
% 3.13/3.35         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 3.13/3.35      inference('simplify', [status(thm)], ['8'])).
% 3.13/3.35  thf('10', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (((k1_tarski @ X0) = (k1_xboole_0))
% 3.13/3.35          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 3.13/3.35          | ((sk_D @ X0 @ (k1_tarski @ X0)) = (X0)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['7', '9'])).
% 3.13/3.35  thf('11', plain,
% 3.13/3.35      (![X25 : $i, X26 : $i]:
% 3.13/3.35         (~ (r2_hidden @ (sk_C_2 @ X25 @ X26) @ X25)
% 3.13/3.35          | ~ (r2_hidden @ (sk_C_2 @ X25 @ X26) @ (sk_D @ X25 @ X26))
% 3.13/3.35          | ((X25) = (k1_setfam_1 @ X26))
% 3.13/3.35          | ((X26) = (k1_xboole_0)))),
% 3.13/3.35      inference('cnf', [status(esa)], [d1_setfam_1])).
% 3.13/3.35  thf('12', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (~ (r2_hidden @ (sk_C_2 @ X0 @ (k1_tarski @ X0)) @ X0)
% 3.13/3.35          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 3.13/3.35          | ((k1_tarski @ X0) = (k1_xboole_0))
% 3.13/3.35          | ((k1_tarski @ X0) = (k1_xboole_0))
% 3.13/3.35          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 3.13/3.35          | ~ (r2_hidden @ (sk_C_2 @ X0 @ (k1_tarski @ X0)) @ X0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['10', '11'])).
% 3.13/3.35  thf('13', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (((k1_tarski @ X0) = (k1_xboole_0))
% 3.13/3.35          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 3.13/3.35          | ~ (r2_hidden @ (sk_C_2 @ X0 @ (k1_tarski @ X0)) @ X0))),
% 3.13/3.35      inference('simplify', [status(thm)], ['12'])).
% 3.13/3.35  thf('14', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         ((r2_hidden @ (sk_C_2 @ X0 @ (k1_tarski @ X0)) @ X0)
% 3.13/3.35          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 3.13/3.35          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 3.13/3.35      inference('eq_fact', [status(thm)], ['3'])).
% 3.13/3.35  thf('15', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 3.13/3.35          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 3.13/3.35      inference('clc', [status(thm)], ['13', '14'])).
% 3.13/3.35  thf(t11_setfam_1, conjecture,
% 3.13/3.35    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 3.13/3.35  thf(zf_stmt_0, negated_conjecture,
% 3.13/3.35    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 3.13/3.35    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 3.13/3.35  thf('16', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('17', plain,
% 3.13/3.35      ((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['15', '16'])).
% 3.13/3.35  thf('18', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 3.13/3.35      inference('simplify', [status(thm)], ['17'])).
% 3.13/3.35  thf('19', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 3.13/3.35      inference('simplify', [status(thm)], ['0'])).
% 3.13/3.35  thf('20', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 3.13/3.35      inference('sup+', [status(thm)], ['18', '19'])).
% 3.13/3.35  thf(d3_tarski, axiom,
% 3.13/3.35    (![A:$i,B:$i]:
% 3.13/3.35     ( ( r1_tarski @ A @ B ) <=>
% 3.13/3.35       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.13/3.35  thf('21', plain,
% 3.13/3.35      (![X1 : $i, X3 : $i]:
% 3.13/3.35         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.13/3.35      inference('cnf', [status(esa)], [d3_tarski])).
% 3.13/3.35  thf(l3_zfmisc_1, axiom,
% 3.13/3.35    (![A:$i,B:$i]:
% 3.13/3.35     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 3.13/3.35       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 3.13/3.35  thf('22', plain,
% 3.13/3.35      (![X19 : $i, X20 : $i]:
% 3.13/3.35         ((r1_tarski @ X19 @ (k1_tarski @ X20)) | ((X19) != (k1_xboole_0)))),
% 3.13/3.35      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 3.13/3.35  thf('23', plain,
% 3.13/3.35      (![X20 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X20))),
% 3.13/3.35      inference('simplify', [status(thm)], ['22'])).
% 3.13/3.35  thf('24', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.13/3.35         (~ (r2_hidden @ X0 @ X1)
% 3.13/3.35          | (r2_hidden @ X0 @ X2)
% 3.13/3.35          | ~ (r1_tarski @ X1 @ X2))),
% 3.13/3.35      inference('cnf', [status(esa)], [d3_tarski])).
% 3.13/3.35  thf('25', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 3.13/3.35          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['23', '24'])).
% 3.13/3.35  thf('26', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         ((r1_tarski @ k1_xboole_0 @ X0)
% 3.13/3.35          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ (k1_tarski @ X1)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['21', '25'])).
% 3.13/3.35  thf('27', plain,
% 3.13/3.35      (![X7 : $i, X10 : $i]:
% 3.13/3.35         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 3.13/3.35      inference('simplify', [status(thm)], ['8'])).
% 3.13/3.35  thf('28', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         ((r1_tarski @ k1_xboole_0 @ X1) | ((sk_C @ X1 @ k1_xboole_0) = (X0)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['26', '27'])).
% 3.13/3.35  thf('29', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 3.13/3.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.13/3.35  thf('30', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         (((sk_C @ X0 @ k1_xboole_0) != (sk_A))
% 3.13/3.35          | (r1_tarski @ k1_xboole_0 @ X0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['28', '29'])).
% 3.13/3.35  thf('31', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         ((r1_tarski @ k1_xboole_0 @ X1) | ((sk_C @ X1 @ k1_xboole_0) = (X0)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['26', '27'])).
% 3.13/3.35  thf('32', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.13/3.35      inference('clc', [status(thm)], ['30', '31'])).
% 3.13/3.35  thf('33', plain,
% 3.13/3.35      (![X1 : $i, X3 : $i]:
% 3.13/3.35         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.13/3.35      inference('cnf', [status(esa)], [d3_tarski])).
% 3.13/3.35  thf(t64_zfmisc_1, axiom,
% 3.13/3.35    (![A:$i,B:$i,C:$i]:
% 3.13/3.35     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 3.13/3.35       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 3.13/3.35  thf('34', plain,
% 3.13/3.35      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.13/3.35         ((r2_hidden @ X21 @ X22)
% 3.13/3.35          | ~ (r2_hidden @ X21 @ (k4_xboole_0 @ X22 @ (k1_tarski @ X23))))),
% 3.13/3.35      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 3.13/3.35  thf('35', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.13/3.35         ((r1_tarski @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X2)
% 3.13/3.35          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))) @ 
% 3.13/3.35             X1))),
% 3.13/3.35      inference('sup-', [status(thm)], ['33', '34'])).
% 3.13/3.35  thf('36', plain,
% 3.13/3.35      (![X1 : $i, X3 : $i]:
% 3.13/3.35         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 3.13/3.35      inference('cnf', [status(esa)], [d3_tarski])).
% 3.13/3.35  thf('37', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         ((r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)
% 3.13/3.35          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0))),
% 3.13/3.35      inference('sup-', [status(thm)], ['35', '36'])).
% 3.13/3.35  thf('38', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)),
% 3.13/3.35      inference('simplify', [status(thm)], ['37'])).
% 3.13/3.35  thf(d10_xboole_0, axiom,
% 3.13/3.35    (![A:$i,B:$i]:
% 3.13/3.35     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.13/3.35  thf('39', plain,
% 3.13/3.35      (![X4 : $i, X6 : $i]:
% 3.13/3.35         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 3.13/3.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.13/3.35  thf('40', plain,
% 3.13/3.35      (![X0 : $i, X1 : $i]:
% 3.13/3.35         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 3.13/3.35          | ((X0) = (k4_xboole_0 @ X0 @ (k1_tarski @ X1))))),
% 3.13/3.35      inference('sup-', [status(thm)], ['38', '39'])).
% 3.13/3.35  thf('41', plain,
% 3.13/3.35      (![X0 : $i]:
% 3.13/3.35         ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 3.13/3.35      inference('sup-', [status(thm)], ['32', '40'])).
% 3.13/3.35  thf('42', plain,
% 3.13/3.35      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.13/3.35         (((X21) != (X23))
% 3.13/3.35          | ~ (r2_hidden @ X21 @ (k4_xboole_0 @ X22 @ (k1_tarski @ X23))))),
% 3.13/3.35      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 3.13/3.35  thf('43', plain,
% 3.13/3.35      (![X22 : $i, X23 : $i]:
% 3.13/3.35         ~ (r2_hidden @ X23 @ (k4_xboole_0 @ X22 @ (k1_tarski @ X23)))),
% 3.13/3.35      inference('simplify', [status(thm)], ['42'])).
% 3.13/3.35  thf('44', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.13/3.35      inference('sup-', [status(thm)], ['41', '43'])).
% 3.13/3.35  thf('45', plain, ($false), inference('sup-', [status(thm)], ['20', '44'])).
% 3.13/3.35  
% 3.13/3.35  % SZS output end Refutation
% 3.13/3.35  
% 3.13/3.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
