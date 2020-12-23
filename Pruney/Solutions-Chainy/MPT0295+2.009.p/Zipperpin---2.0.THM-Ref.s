%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r1GxGEPxna

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:57 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 170 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  502 (1800 expanded)
%              Number of equality atoms :   16 (  49 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(t103_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ D @ A )
        & ! [E: $i,F: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
          & ( r2_hidden @ D @ A )
          & ! [E: $i,F: $i] :
              ~ ( ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C )
                & ( D
                  = ( k4_tarski @ E @ F ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t103_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_2 @ X0 )
      | ( r2_hidden @ sk_D_2 @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 )
      | ( r1_xboole_0 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    r2_hidden @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r2_hidden @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D_2 @ ( k4_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    r2_hidden @ sk_D_2 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','25'])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X25 @ X22 @ X23 ) @ ( sk_E_1 @ X25 @ X22 @ X23 ) @ X25 @ X22 @ X23 )
      | ( X24
       != ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X25 @ X22 @ X23 ) @ ( sk_E_1 @ X25 @ X22 @ X23 ) @ X25 @ X22 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_2 @ sk_C_1 @ sk_B ) @ ( sk_E_1 @ sk_D_2 @ sk_C_1 @ sk_B ) @ sk_D_2 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15
        = ( k4_tarski @ X13 @ X14 ) )
      | ~ ( zip_tseitin_0 @ X14 @ X13 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,
    ( sk_D_2
    = ( k4_tarski @ ( sk_E_1 @ sk_D_2 @ sk_C_1 @ sk_B ) @ ( sk_F_1 @ sk_D_2 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_2 @ sk_C_1 @ sk_B ) @ ( sk_E_1 @ sk_D_2 @ sk_C_1 @ sk_B ) @ sk_D_2 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['26','28'])).

thf('33',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X13 @ X17 )
      | ~ ( zip_tseitin_0 @ X14 @ X13 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    r2_hidden @ ( sk_E_1 @ sk_D_2 @ sk_C_1 @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ sk_B )
      | ( sk_D_2
       != ( k4_tarski @ X29 @ X30 ) )
      | ~ ( r2_hidden @ X30 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( sk_D_2
       != ( k4_tarski @ ( sk_E_1 @ sk_D_2 @ sk_C_1 @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_D_2 != sk_D_2 )
    | ~ ( r2_hidden @ ( sk_F_1 @ sk_D_2 @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_D_2 @ sk_C_1 @ sk_B ) @ ( sk_E_1 @ sk_D_2 @ sk_C_1 @ sk_B ) @ sk_D_2 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['26','28'])).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ X16 )
      | ~ ( zip_tseitin_0 @ X14 @ X13 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,(
    r2_hidden @ ( sk_F_1 @ sk_D_2 @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    sk_D_2 != sk_D_2 ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r1GxGEPxna
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:37:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.91/1.13  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.13  % Solved by: fo/fo7.sh
% 0.91/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.13  % done 1653 iterations in 0.670s
% 0.91/1.13  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.13  % SZS output start Refutation
% 0.91/1.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.13  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.91/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.13  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.91/1.13  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.91/1.13  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.91/1.13  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.13  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.91/1.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.13  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.91/1.13  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.91/1.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.13  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.91/1.13  thf(t103_zfmisc_1, conjecture,
% 0.91/1.13    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.13     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.91/1.13          ( r2_hidden @ D @ A ) & 
% 0.91/1.13          ( ![E:$i,F:$i]:
% 0.91/1.13            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.91/1.13                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.91/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.13    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.13        ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.91/1.13             ( r2_hidden @ D @ A ) & 
% 0.91/1.13             ( ![E:$i,F:$i]:
% 0.91/1.13               ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.91/1.13                    ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ) )),
% 0.91/1.13    inference('cnf.neg', [status(esa)], [t103_zfmisc_1])).
% 0.91/1.13  thf('0', plain, ((r2_hidden @ sk_D_2 @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf(d5_xboole_0, axiom,
% 0.91/1.13    (![A:$i,B:$i,C:$i]:
% 0.91/1.13     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.91/1.13       ( ![D:$i]:
% 0.91/1.13         ( ( r2_hidden @ D @ C ) <=>
% 0.91/1.13           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.91/1.13  thf('1', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.91/1.13         (~ (r2_hidden @ X0 @ X1)
% 0.91/1.13          | (r2_hidden @ X0 @ X2)
% 0.91/1.13          | (r2_hidden @ X0 @ X3)
% 0.91/1.13          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.91/1.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.91/1.13  thf('2', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.13         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.91/1.13          | (r2_hidden @ X0 @ X2)
% 0.91/1.13          | ~ (r2_hidden @ X0 @ X1))),
% 0.91/1.13      inference('simplify', [status(thm)], ['1'])).
% 0.91/1.13  thf('3', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         ((r2_hidden @ sk_D_2 @ X0)
% 0.91/1.13          | (r2_hidden @ sk_D_2 @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['0', '2'])).
% 0.91/1.13  thf(t3_xboole_0, axiom,
% 0.91/1.13    (![A:$i,B:$i]:
% 0.91/1.13     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.91/1.13            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.13       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.91/1.13            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.91/1.13  thf('4', plain,
% 0.91/1.13      (![X6 : $i, X7 : $i]:
% 0.91/1.13         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.91/1.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.13  thf('5', plain,
% 0.91/1.13      (![X6 : $i, X7 : $i]:
% 0.91/1.13         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.91/1.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.13  thf('6', plain,
% 0.91/1.13      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.13         (~ (r2_hidden @ X4 @ X3)
% 0.91/1.13          | ~ (r2_hidden @ X4 @ X2)
% 0.91/1.13          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.91/1.13      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.91/1.13  thf('7', plain,
% 0.91/1.13      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.91/1.13         (~ (r2_hidden @ X4 @ X2)
% 0.91/1.13          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.91/1.13      inference('simplify', [status(thm)], ['6'])).
% 0.91/1.13  thf('8', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.13         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.91/1.13          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['5', '7'])).
% 0.91/1.13  thf('9', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.91/1.13          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['4', '8'])).
% 0.91/1.13  thf('10', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.91/1.13      inference('simplify', [status(thm)], ['9'])).
% 0.91/1.13  thf('11', plain,
% 0.91/1.13      (![X6 : $i, X7 : $i]:
% 0.91/1.13         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.91/1.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.13  thf('12', plain,
% 0.91/1.13      (![X6 : $i, X7 : $i]:
% 0.91/1.13         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.91/1.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.13  thf('13', plain,
% 0.91/1.13      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.91/1.13         (~ (r2_hidden @ X8 @ X6)
% 0.91/1.13          | ~ (r2_hidden @ X8 @ X9)
% 0.91/1.13          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.91/1.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.13  thf('14', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.13         ((r1_xboole_0 @ X1 @ X0)
% 0.91/1.13          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.91/1.13          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.91/1.13      inference('sup-', [status(thm)], ['12', '13'])).
% 0.91/1.13  thf('15', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         ((r1_xboole_0 @ X0 @ X1)
% 0.91/1.13          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.91/1.13          | (r1_xboole_0 @ X0 @ X1))),
% 0.91/1.13      inference('sup-', [status(thm)], ['11', '14'])).
% 0.91/1.13  thf('16', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]:
% 0.91/1.13         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.91/1.13      inference('simplify', [status(thm)], ['15'])).
% 0.91/1.13  thf('17', plain,
% 0.91/1.13      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['10', '16'])).
% 0.91/1.13  thf('18', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf(t63_xboole_1, axiom,
% 0.91/1.13    (![A:$i,B:$i,C:$i]:
% 0.91/1.13     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.91/1.13       ( r1_xboole_0 @ A @ C ) ))).
% 0.91/1.13  thf('19', plain,
% 0.91/1.13      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.91/1.13         (~ (r1_tarski @ X10 @ X11)
% 0.91/1.13          | ~ (r1_xboole_0 @ X11 @ X12)
% 0.91/1.13          | (r1_xboole_0 @ X10 @ X12))),
% 0.91/1.13      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.91/1.13  thf('20', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         ((r1_xboole_0 @ sk_A @ X0)
% 0.91/1.13          | ~ (r1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C_1) @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['18', '19'])).
% 0.91/1.13  thf('21', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (r1_xboole_0 @ sk_A @ 
% 0.91/1.13          (k4_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['17', '20'])).
% 0.91/1.13  thf('22', plain, ((r2_hidden @ sk_D_2 @ sk_A)),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('23', plain,
% 0.91/1.13      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.91/1.13         (~ (r2_hidden @ X8 @ X6)
% 0.91/1.13          | ~ (r2_hidden @ X8 @ X9)
% 0.91/1.13          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.91/1.13      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.91/1.13  thf('24', plain,
% 0.91/1.13      (![X0 : $i]: (~ (r1_xboole_0 @ sk_A @ X0) | ~ (r2_hidden @ sk_D_2 @ X0))),
% 0.91/1.13      inference('sup-', [status(thm)], ['22', '23'])).
% 0.91/1.13  thf('25', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         ~ (r2_hidden @ sk_D_2 @ 
% 0.91/1.13            (k4_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['21', '24'])).
% 0.91/1.13  thf('26', plain, ((r2_hidden @ sk_D_2 @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.91/1.13      inference('sup-', [status(thm)], ['3', '25'])).
% 0.91/1.13  thf(d2_zfmisc_1, axiom,
% 0.91/1.13    (![A:$i,B:$i,C:$i]:
% 0.91/1.13     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.91/1.13       ( ![D:$i]:
% 0.91/1.13         ( ( r2_hidden @ D @ C ) <=>
% 0.91/1.13           ( ?[E:$i,F:$i]:
% 0.91/1.13             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.91/1.13               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.91/1.13  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.91/1.13  thf(zf_stmt_2, axiom,
% 0.91/1.13    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.91/1.13     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.91/1.13       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.91/1.13         ( r2_hidden @ E @ A ) ) ))).
% 0.91/1.13  thf(zf_stmt_3, axiom,
% 0.91/1.13    (![A:$i,B:$i,C:$i]:
% 0.91/1.13     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.91/1.13       ( ![D:$i]:
% 0.91/1.13         ( ( r2_hidden @ D @ C ) <=>
% 0.91/1.13           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.91/1.13  thf('27', plain,
% 0.91/1.13      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.91/1.13         (~ (r2_hidden @ X25 @ X24)
% 0.91/1.13          | (zip_tseitin_0 @ (sk_F_1 @ X25 @ X22 @ X23) @ 
% 0.91/1.13             (sk_E_1 @ X25 @ X22 @ X23) @ X25 @ X22 @ X23)
% 0.91/1.13          | ((X24) != (k2_zfmisc_1 @ X23 @ X22)))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.13  thf('28', plain,
% 0.91/1.13      (![X22 : $i, X23 : $i, X25 : $i]:
% 0.91/1.13         ((zip_tseitin_0 @ (sk_F_1 @ X25 @ X22 @ X23) @ 
% 0.91/1.13           (sk_E_1 @ X25 @ X22 @ X23) @ X25 @ X22 @ X23)
% 0.91/1.13          | ~ (r2_hidden @ X25 @ (k2_zfmisc_1 @ X23 @ X22)))),
% 0.91/1.13      inference('simplify', [status(thm)], ['27'])).
% 0.91/1.13  thf('29', plain,
% 0.91/1.13      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_2 @ sk_C_1 @ sk_B) @ 
% 0.91/1.13        (sk_E_1 @ sk_D_2 @ sk_C_1 @ sk_B) @ sk_D_2 @ sk_C_1 @ sk_B)),
% 0.91/1.13      inference('sup-', [status(thm)], ['26', '28'])).
% 0.91/1.13  thf('30', plain,
% 0.91/1.13      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.91/1.13         (((X15) = (k4_tarski @ X13 @ X14))
% 0.91/1.13          | ~ (zip_tseitin_0 @ X14 @ X13 @ X15 @ X16 @ X17))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.91/1.13  thf('31', plain,
% 0.91/1.13      (((sk_D_2)
% 0.91/1.13         = (k4_tarski @ (sk_E_1 @ sk_D_2 @ sk_C_1 @ sk_B) @ 
% 0.91/1.13            (sk_F_1 @ sk_D_2 @ sk_C_1 @ sk_B)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['29', '30'])).
% 0.91/1.13  thf('32', plain,
% 0.91/1.13      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_2 @ sk_C_1 @ sk_B) @ 
% 0.91/1.13        (sk_E_1 @ sk_D_2 @ sk_C_1 @ sk_B) @ sk_D_2 @ sk_C_1 @ sk_B)),
% 0.91/1.13      inference('sup-', [status(thm)], ['26', '28'])).
% 0.91/1.13  thf('33', plain,
% 0.91/1.13      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.91/1.13         ((r2_hidden @ X13 @ X17)
% 0.91/1.13          | ~ (zip_tseitin_0 @ X14 @ X13 @ X15 @ X16 @ X17))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.91/1.13  thf('34', plain, ((r2_hidden @ (sk_E_1 @ sk_D_2 @ sk_C_1 @ sk_B) @ sk_B)),
% 0.91/1.13      inference('sup-', [status(thm)], ['32', '33'])).
% 0.91/1.13  thf('35', plain,
% 0.91/1.13      (![X29 : $i, X30 : $i]:
% 0.91/1.13         (~ (r2_hidden @ X29 @ sk_B)
% 0.91/1.13          | ((sk_D_2) != (k4_tarski @ X29 @ X30))
% 0.91/1.13          | ~ (r2_hidden @ X30 @ sk_C_1))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.13  thf('36', plain,
% 0.91/1.13      (![X0 : $i]:
% 0.91/1.13         (~ (r2_hidden @ X0 @ sk_C_1)
% 0.91/1.13          | ((sk_D_2) != (k4_tarski @ (sk_E_1 @ sk_D_2 @ sk_C_1 @ sk_B) @ X0)))),
% 0.91/1.13      inference('sup-', [status(thm)], ['34', '35'])).
% 0.91/1.13  thf('37', plain,
% 0.91/1.13      ((((sk_D_2) != (sk_D_2))
% 0.91/1.13        | ~ (r2_hidden @ (sk_F_1 @ sk_D_2 @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.91/1.13      inference('sup-', [status(thm)], ['31', '36'])).
% 0.91/1.13  thf('38', plain,
% 0.91/1.13      ((zip_tseitin_0 @ (sk_F_1 @ sk_D_2 @ sk_C_1 @ sk_B) @ 
% 0.91/1.13        (sk_E_1 @ sk_D_2 @ sk_C_1 @ sk_B) @ sk_D_2 @ sk_C_1 @ sk_B)),
% 0.91/1.13      inference('sup-', [status(thm)], ['26', '28'])).
% 0.91/1.13  thf('39', plain,
% 0.91/1.13      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.91/1.13         ((r2_hidden @ X14 @ X16)
% 0.91/1.13          | ~ (zip_tseitin_0 @ X14 @ X13 @ X15 @ X16 @ X17))),
% 0.91/1.13      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.91/1.13  thf('40', plain, ((r2_hidden @ (sk_F_1 @ sk_D_2 @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.91/1.13      inference('sup-', [status(thm)], ['38', '39'])).
% 0.91/1.13  thf('41', plain, (((sk_D_2) != (sk_D_2))),
% 0.91/1.13      inference('demod', [status(thm)], ['37', '40'])).
% 0.91/1.13  thf('42', plain, ($false), inference('simplify', [status(thm)], ['41'])).
% 0.91/1.13  
% 0.91/1.13  % SZS output end Refutation
% 0.91/1.13  
% 0.98/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
