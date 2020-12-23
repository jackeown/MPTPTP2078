%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7h3tx4y8d6

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:59 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 162 expanded)
%              Number of leaves         :   18 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :  737 (2792 expanded)
%              Number of equality atoms :   32 ( 143 expanded)
%              Maximal formula depth    :   15 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ( X13
        = ( k2_zfmisc_1 @ X10 @ X9 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X13 @ X9 @ X10 ) @ ( sk_E @ X13 @ X9 @ X10 ) @ ( sk_D @ X13 @ X9 @ X10 ) @ X9 @ X10 )
      | ( r2_hidden @ ( sk_D @ X13 @ X9 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2
        = ( k4_tarski @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( ( sk_D @ X2 @ X1 @ X0 )
        = ( k4_tarski @ ( sk_E @ X2 @ X1 @ X0 ) @ ( sk_F @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ( X13
        = ( k2_zfmisc_1 @ X10 @ X9 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X13 @ X9 @ X10 ) @ ( sk_E @ X13 @ X9 @ X10 ) @ ( sk_D @ X13 @ X9 @ X10 ) @ X9 @ X10 )
      | ( r2_hidden @ ( sk_D @ X13 @ X9 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X10 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( ( sk_D @ X2 @ X1 @ X0 )
        = ( k4_tarski @ ( sk_E @ X2 @ X1 @ X0 ) @ ( sk_F @ X2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t108_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ! [E: $i,F: $i] :
          ( ( r2_hidden @ ( k4_tarski @ E @ F ) @ ( k2_zfmisc_1 @ A @ B ) )
        <=> ( r2_hidden @ ( k4_tarski @ E @ F ) @ ( k2_zfmisc_1 @ C @ D ) ) )
     => ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ! [E: $i,F: $i] :
            ( ( r2_hidden @ ( k4_tarski @ E @ F ) @ ( k2_zfmisc_1 @ A @ B ) )
          <=> ( r2_hidden @ ( k4_tarski @ E @ F ) @ ( k2_zfmisc_1 @ C @ D ) ) )
       => ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ C @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t108_zfmisc_1])).

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X17 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X2 @ X1 @ X0 ) @ ( sk_F @ X2 @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_D_1 @ sk_C ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X0 @ sk_D_1 @ sk_C ) @ ( sk_F @ X0 @ sk_D_1 @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_D_1 @ sk_C ) @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X0 @ sk_D_1 @ sk_C ) @ ( sk_F @ X0 @ sk_D_1 @ sk_C ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_D_1 @ sk_C ) @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_D_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( X0
        = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_D_1 @ sk_C ) @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_D_1 @ sk_C ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_D_1 @ sk_C ) @ X0 )
      | ( X0
        = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_D_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) )
    | ( r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('15',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('18',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ sk_B @ sk_A ) @ ( sk_E_1 @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ sk_B @ sk_A ) @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2
        = ( k4_tarski @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,
    ( ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C )
    = ( k4_tarski @ ( sk_E_1 @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ sk_B @ sk_A ) @ ( sk_F_1 @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ sk_B @ sk_A ) @ ( sk_F_1 @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('25',plain,
    ( ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C )
    = ( k4_tarski @ ( sk_E_1 @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ sk_B @ sk_A ) @ ( sk_F_1 @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('26',plain,(
    r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('28',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ sk_D_1 @ sk_C ) @ ( sk_E_1 @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ sk_D_1 @ sk_C ) @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ sk_D_1 @ sk_C ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X9: $i,X10: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13
        = ( k2_zfmisc_1 @ X10 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ ( sk_D @ X13 @ X9 @ X10 ) @ X9 @ X10 )
      | ~ ( r2_hidden @ ( sk_D @ X13 @ X9 @ X10 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('30',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_D_1 @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('32',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != ( k2_zfmisc_1 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7h3tx4y8d6
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.57  % Solved by: fo/fo7.sh
% 0.35/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.57  % done 77 iterations in 0.142s
% 0.35/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.57  % SZS output start Refutation
% 0.35/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.57  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.35/0.57  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.35/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.57  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.35/0.57  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.35/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.35/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.35/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.35/0.57  thf(d2_zfmisc_1, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.35/0.57       ( ![D:$i]:
% 0.35/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.57           ( ?[E:$i,F:$i]:
% 0.35/0.57             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.35/0.57               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.35/0.57  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.35/0.57  thf(zf_stmt_1, axiom,
% 0.35/0.57    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.35/0.57     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.35/0.57       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.35/0.57         ( r2_hidden @ E @ A ) ) ))).
% 0.35/0.57  thf(zf_stmt_2, axiom,
% 0.35/0.57    (![A:$i,B:$i,C:$i]:
% 0.35/0.57     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.35/0.57       ( ![D:$i]:
% 0.35/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.57           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.35/0.57  thf('0', plain,
% 0.35/0.57      (![X9 : $i, X10 : $i, X13 : $i]:
% 0.35/0.57         (((X13) = (k2_zfmisc_1 @ X10 @ X9))
% 0.35/0.57          | (zip_tseitin_0 @ (sk_F @ X13 @ X9 @ X10) @ 
% 0.35/0.57             (sk_E @ X13 @ X9 @ X10) @ (sk_D @ X13 @ X9 @ X10) @ X9 @ X10)
% 0.35/0.57          | (r2_hidden @ (sk_D @ X13 @ X9 @ X10) @ X13))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.57  thf('1', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.57         (((X2) = (k4_tarski @ X0 @ X1))
% 0.35/0.57          | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf('2', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.57         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.35/0.57          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.35/0.57          | ((sk_D @ X2 @ X1 @ X0)
% 0.35/0.57              = (k4_tarski @ (sk_E @ X2 @ X1 @ X0) @ (sk_F @ X2 @ X1 @ X0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.57  thf('3', plain,
% 0.35/0.57      (![X9 : $i, X10 : $i, X13 : $i]:
% 0.35/0.57         (((X13) = (k2_zfmisc_1 @ X10 @ X9))
% 0.35/0.57          | (zip_tseitin_0 @ (sk_F @ X13 @ X9 @ X10) @ 
% 0.35/0.57             (sk_E @ X13 @ X9 @ X10) @ (sk_D @ X13 @ X9 @ X10) @ X9 @ X10)
% 0.35/0.57          | (r2_hidden @ (sk_D @ X13 @ X9 @ X10) @ X13))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.57  thf('4', plain,
% 0.35/0.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.57         (~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10)
% 0.35/0.57          | (r2_hidden @ X8 @ X11)
% 0.35/0.57          | ((X11) != (k2_zfmisc_1 @ X10 @ X9)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.57  thf('5', plain,
% 0.35/0.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.57         ((r2_hidden @ X8 @ (k2_zfmisc_1 @ X10 @ X9))
% 0.35/0.57          | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 @ X10))),
% 0.35/0.57      inference('simplify', [status(thm)], ['4'])).
% 0.35/0.57  thf('6', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.57         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.35/0.57          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.35/0.57          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['3', '5'])).
% 0.35/0.57  thf('7', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.57         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.35/0.57          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.35/0.57          | ((sk_D @ X2 @ X1 @ X0)
% 0.35/0.57              = (k4_tarski @ (sk_E @ X2 @ X1 @ X0) @ (sk_F @ X2 @ X1 @ X0))))),
% 0.35/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.57  thf(t108_zfmisc_1, conjecture,
% 0.35/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.57     ( ( ![E:$i,F:$i]:
% 0.35/0.57         ( ( r2_hidden @ ( k4_tarski @ E @ F ) @ ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.35/0.57           ( r2_hidden @ ( k4_tarski @ E @ F ) @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.35/0.57       ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) ))).
% 0.35/0.57  thf(zf_stmt_3, negated_conjecture,
% 0.35/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.57        ( ( ![E:$i,F:$i]:
% 0.35/0.57            ( ( r2_hidden @ ( k4_tarski @ E @ F ) @ ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.35/0.57              ( r2_hidden @ ( k4_tarski @ E @ F ) @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.35/0.57          ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) ) )),
% 0.35/0.57    inference('cnf.neg', [status(esa)], [t108_zfmisc_1])).
% 0.35/0.57  thf('8', plain,
% 0.35/0.57      (![X16 : $i, X17 : $i]:
% 0.35/0.57         ((r2_hidden @ (k4_tarski @ X16 @ X17) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.35/0.57          | ~ (r2_hidden @ (k4_tarski @ X16 @ X17) @ 
% 0.35/0.57               (k2_zfmisc_1 @ sk_C @ sk_D_1)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.57  thf('9', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.57         (~ (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C @ sk_D_1))
% 0.35/0.57          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.35/0.57          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.35/0.57          | (r2_hidden @ 
% 0.35/0.57             (k4_tarski @ (sk_E @ X2 @ X1 @ X0) @ (sk_F @ X2 @ X1 @ X0)) @ 
% 0.35/0.57             (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.57  thf('10', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         (((X0) = (k2_zfmisc_1 @ sk_C @ sk_D_1))
% 0.35/0.57          | (r2_hidden @ (sk_D @ X0 @ sk_D_1 @ sk_C) @ X0)
% 0.35/0.57          | (r2_hidden @ 
% 0.35/0.57             (k4_tarski @ (sk_E @ X0 @ sk_D_1 @ sk_C) @ 
% 0.35/0.57              (sk_F @ X0 @ sk_D_1 @ sk_C)) @ 
% 0.35/0.57             (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.35/0.57          | (r2_hidden @ (sk_D @ X0 @ sk_D_1 @ sk_C) @ X0)
% 0.35/0.57          | ((X0) = (k2_zfmisc_1 @ sk_C @ sk_D_1)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['6', '9'])).
% 0.35/0.57  thf('11', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((r2_hidden @ 
% 0.35/0.57           (k4_tarski @ (sk_E @ X0 @ sk_D_1 @ sk_C) @ 
% 0.35/0.57            (sk_F @ X0 @ sk_D_1 @ sk_C)) @ 
% 0.35/0.57           (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.35/0.57          | (r2_hidden @ (sk_D @ X0 @ sk_D_1 @ sk_C) @ X0)
% 0.35/0.57          | ((X0) = (k2_zfmisc_1 @ sk_C @ sk_D_1)))),
% 0.35/0.57      inference('simplify', [status(thm)], ['10'])).
% 0.35/0.57  thf('12', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((r2_hidden @ (sk_D @ X0 @ sk_D_1 @ sk_C) @ 
% 0.35/0.57           (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.35/0.57          | ((X0) = (k2_zfmisc_1 @ sk_C @ sk_D_1))
% 0.35/0.57          | (r2_hidden @ (sk_D @ X0 @ sk_D_1 @ sk_C) @ X0)
% 0.35/0.57          | ((X0) = (k2_zfmisc_1 @ sk_C @ sk_D_1))
% 0.35/0.57          | (r2_hidden @ (sk_D @ X0 @ sk_D_1 @ sk_C) @ X0))),
% 0.35/0.57      inference('sup+', [status(thm)], ['2', '11'])).
% 0.35/0.57  thf('13', plain,
% 0.35/0.57      (![X0 : $i]:
% 0.35/0.57         ((r2_hidden @ (sk_D @ X0 @ sk_D_1 @ sk_C) @ X0)
% 0.35/0.57          | ((X0) = (k2_zfmisc_1 @ sk_C @ sk_D_1))
% 0.35/0.57          | (r2_hidden @ (sk_D @ X0 @ sk_D_1 @ sk_C) @ 
% 0.35/0.57             (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('simplify', [status(thm)], ['12'])).
% 0.35/0.57  thf('14', plain,
% 0.35/0.57      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D_1))
% 0.35/0.57        | (r2_hidden @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57           (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('eq_fact', [status(thm)], ['13'])).
% 0.35/0.57  thf('15', plain,
% 0.35/0.57      (((k2_zfmisc_1 @ sk_A @ sk_B) != (k2_zfmisc_1 @ sk_C @ sk_D_1))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.57  thf('16', plain,
% 0.35/0.57      ((r2_hidden @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.35/0.57      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.35/0.57  thf('17', plain,
% 0.35/0.57      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.57         (~ (r2_hidden @ X12 @ X11)
% 0.35/0.57          | (zip_tseitin_0 @ (sk_F_1 @ X12 @ X9 @ X10) @ 
% 0.35/0.57             (sk_E_1 @ X12 @ X9 @ X10) @ X12 @ X9 @ X10)
% 0.35/0.57          | ((X11) != (k2_zfmisc_1 @ X10 @ X9)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.57  thf('18', plain,
% 0.35/0.57      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.35/0.57         ((zip_tseitin_0 @ (sk_F_1 @ X12 @ X9 @ X10) @ 
% 0.35/0.57           (sk_E_1 @ X12 @ X9 @ X10) @ X12 @ X9 @ X10)
% 0.35/0.57          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X10 @ X9)))),
% 0.35/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.35/0.57  thf('19', plain,
% 0.35/0.57      ((zip_tseitin_0 @ 
% 0.35/0.57        (sk_F_1 @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57         sk_B @ sk_A) @ 
% 0.35/0.57        (sk_E_1 @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57         sk_B @ sk_A) @ 
% 0.35/0.57        (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ sk_B @ sk_A)),
% 0.35/0.57      inference('sup-', [status(thm)], ['16', '18'])).
% 0.35/0.57  thf('20', plain,
% 0.35/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.57         (((X2) = (k4_tarski @ X0 @ X1))
% 0.35/0.57          | ~ (zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.35/0.57  thf('21', plain,
% 0.35/0.57      (((sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C)
% 0.35/0.57         = (k4_tarski @ 
% 0.35/0.57            (sk_E_1 @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57             sk_B @ sk_A) @ 
% 0.35/0.57            (sk_F_1 @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57             sk_B @ sk_A)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.57  thf('22', plain,
% 0.35/0.57      (![X16 : $i, X18 : $i]:
% 0.35/0.57         ((r2_hidden @ (k4_tarski @ X16 @ X18) @ (k2_zfmisc_1 @ sk_C @ sk_D_1))
% 0.35/0.57          | ~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ 
% 0.35/0.57               (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.57  thf('23', plain,
% 0.35/0.57      ((~ (r2_hidden @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57           (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.35/0.57        | (r2_hidden @ 
% 0.35/0.57           (k4_tarski @ 
% 0.35/0.57            (sk_E_1 @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57             sk_B @ sk_A) @ 
% 0.35/0.57            (sk_F_1 @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57             sk_B @ sk_A)) @ 
% 0.35/0.57           (k2_zfmisc_1 @ sk_C @ sk_D_1)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.57  thf('24', plain,
% 0.35/0.57      ((r2_hidden @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.35/0.57      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.35/0.57  thf('25', plain,
% 0.35/0.57      (((sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C)
% 0.35/0.57         = (k4_tarski @ 
% 0.35/0.57            (sk_E_1 @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57             sk_B @ sk_A) @ 
% 0.35/0.57            (sk_F_1 @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57             sk_B @ sk_A)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.35/0.57  thf('26', plain,
% 0.35/0.57      ((r2_hidden @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57        (k2_zfmisc_1 @ sk_C @ sk_D_1))),
% 0.35/0.57      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.35/0.57  thf('27', plain,
% 0.35/0.57      (![X9 : $i, X10 : $i, X12 : $i]:
% 0.35/0.57         ((zip_tseitin_0 @ (sk_F_1 @ X12 @ X9 @ X10) @ 
% 0.35/0.57           (sk_E_1 @ X12 @ X9 @ X10) @ X12 @ X9 @ X10)
% 0.35/0.57          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X10 @ X9)))),
% 0.35/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.35/0.57  thf('28', plain,
% 0.35/0.57      ((zip_tseitin_0 @ 
% 0.35/0.57        (sk_F_1 @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57         sk_D_1 @ sk_C) @ 
% 0.35/0.57        (sk_E_1 @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57         sk_D_1 @ sk_C) @ 
% 0.35/0.57        (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ sk_D_1 @ sk_C)),
% 0.35/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.57  thf('29', plain,
% 0.35/0.57      (![X9 : $i, X10 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.35/0.57         (((X13) = (k2_zfmisc_1 @ X10 @ X9))
% 0.35/0.57          | ~ (zip_tseitin_0 @ X14 @ X15 @ (sk_D @ X13 @ X9 @ X10) @ X9 @ X10)
% 0.35/0.57          | ~ (r2_hidden @ (sk_D @ X13 @ X9 @ X10) @ X13))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.57  thf('30', plain,
% 0.35/0.57      ((~ (r2_hidden @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57           (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.35/0.57        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D_1)))),
% 0.35/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.35/0.57  thf('31', plain,
% 0.35/0.57      ((r2_hidden @ (sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_D_1 @ sk_C) @ 
% 0.35/0.57        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.35/0.57      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.35/0.57  thf('32', plain,
% 0.35/0.57      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D_1))),
% 0.35/0.57      inference('demod', [status(thm)], ['30', '31'])).
% 0.35/0.57  thf('33', plain,
% 0.35/0.57      (((k2_zfmisc_1 @ sk_A @ sk_B) != (k2_zfmisc_1 @ sk_C @ sk_D_1))),
% 0.35/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.35/0.57  thf('34', plain, ($false),
% 0.35/0.57      inference('simplify_reflect-', [status(thm)], ['32', '33'])).
% 0.35/0.57  
% 0.35/0.57  % SZS output end Refutation
% 0.35/0.57  
% 0.35/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
