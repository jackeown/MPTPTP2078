%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XMz3hndBRZ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:58 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 121 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :  506 (1343 expanded)
%              Number of equality atoms :   18 (  62 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t104_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ~ ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ B @ C ) @ ( k2_zfmisc_1 @ D @ E ) ) )
        & ! [F: $i,G: $i] :
            ~ ( ( A
                = ( k4_tarski @ F @ G ) )
              & ( r2_hidden @ F @ ( k3_xboole_0 @ B @ D ) )
              & ( r2_hidden @ G @ ( k3_xboole_0 @ C @ E ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ~ ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ B @ C ) @ ( k2_zfmisc_1 @ D @ E ) ) )
          & ! [F: $i,G: $i] :
              ~ ( ( A
                  = ( k4_tarski @ F @ G ) )
                & ( r2_hidden @ F @ ( k3_xboole_0 @ B @ D ) )
                & ( r2_hidden @ G @ ( k3_xboole_0 @ C @ E ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t104_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t103_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r2_hidden @ D @ A )
        & ! [E: $i,F: $i] :
            ~ ( ( r2_hidden @ E @ B )
              & ( r2_hidden @ F @ C )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) )
      | ( X19
        = ( k4_tarski @ ( sk_E @ X19 @ X18 @ X17 ) @ ( sk_F @ X19 @ X18 @ X17 ) ) )
      | ~ ( r2_hidden @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( X2
        = ( k4_tarski @ ( sk_E @ X2 @ X0 @ X1 ) @ ( sk_F @ X2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E @ sk_A @ sk_E_1 @ sk_D_1 ) @ ( sk_F @ sk_A @ sk_E_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E @ sk_A @ sk_E_1 @ sk_D_1 ) @ ( sk_F @ sk_A @ sk_E_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ sk_A @ sk_E_1 @ sk_D_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( sk_E @ sk_A @ sk_E_1 @ sk_D_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('18',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) )
      | ( r2_hidden @ ( sk_E @ X19 @ X18 @ X17 ) @ X17 )
      | ~ ( r2_hidden @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( sk_E @ sk_A @ sk_E_1 @ sk_D_1 ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ sk_A @ sk_E_1 @ sk_D_1 ) @ X0 )
      | ( r2_hidden @ ( sk_E @ sk_A @ sk_E_1 @ sk_D_1 ) @ ( k3_xboole_0 @ X0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    r2_hidden @ ( sk_E @ sk_A @ sk_E_1 @ sk_D_1 ) @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k3_xboole_0 @ sk_B @ sk_D_1 ) )
      | ~ ( r2_hidden @ X21 @ ( k3_xboole_0 @ sk_C @ sk_E_1 ) )
      | ( sk_A
       != ( k4_tarski @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_E @ sk_A @ sk_E_1 @ sk_D_1 ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_C @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_F @ sk_A @ sk_E_1 @ sk_D_1 ) @ ( k3_xboole_0 @ sk_C @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['8','27'])).

thf('29',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('30',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E @ sk_A @ sk_E_1 @ sk_D_1 ) @ ( sk_F @ sk_A @ sk_E_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X13 ) @ ( k2_zfmisc_1 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ sk_A @ sk_E_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ ( sk_F @ sk_A @ sk_E_1 @ sk_D_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_D_1 @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('35',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) )
      | ( r2_hidden @ ( sk_F @ X19 @ X18 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t103_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ ( sk_F @ sk_A @ sk_E_1 @ sk_D_1 ) @ sk_E_1 ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_F @ sk_A @ sk_E_1 @ sk_D_1 ) @ X0 )
      | ( r2_hidden @ ( sk_F @ sk_A @ sk_E_1 @ sk_D_1 ) @ ( k3_xboole_0 @ X0 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r2_hidden @ ( sk_F @ sk_A @ sk_E_1 @ sk_D_1 ) @ ( k3_xboole_0 @ sk_C @ sk_E_1 ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['28','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XMz3hndBRZ
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:19:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 289 iterations in 0.224s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.68  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.68  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.46/0.68  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.46/0.68  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.46/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(t104_zfmisc_1, conjecture,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.46/0.68     ( ~( ( r2_hidden @
% 0.46/0.68            A @ 
% 0.46/0.68            ( k3_xboole_0 @ ( k2_zfmisc_1 @ B @ C ) @ ( k2_zfmisc_1 @ D @ E ) ) ) & 
% 0.46/0.68          ( ![F:$i,G:$i]:
% 0.46/0.68            ( ~( ( ( A ) = ( k4_tarski @ F @ G ) ) & 
% 0.46/0.68                 ( r2_hidden @ F @ ( k3_xboole_0 @ B @ D ) ) & 
% 0.46/0.68                 ( r2_hidden @ G @ ( k3_xboole_0 @ C @ E ) ) ) ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.46/0.68        ( ~( ( r2_hidden @
% 0.46/0.68               A @ 
% 0.46/0.68               ( k3_xboole_0 @
% 0.46/0.68                 ( k2_zfmisc_1 @ B @ C ) @ ( k2_zfmisc_1 @ D @ E ) ) ) & 
% 0.46/0.68             ( ![F:$i,G:$i]:
% 0.46/0.68               ( ~( ( ( A ) = ( k4_tarski @ F @ G ) ) & 
% 0.46/0.68                    ( r2_hidden @ F @ ( k3_xboole_0 @ B @ D ) ) & 
% 0.46/0.68                    ( r2_hidden @ G @ ( k3_xboole_0 @ C @ E ) ) ) ) ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t104_zfmisc_1])).
% 0.46/0.68  thf('0', plain,
% 0.46/0.68      ((r2_hidden @ sk_A @ 
% 0.46/0.68        (k3_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ 
% 0.46/0.68         (k2_zfmisc_1 @ sk_D_1 @ sk_E_1)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(d4_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.46/0.68       ( ![D:$i]:
% 0.46/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.68           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.46/0.68  thf('1', plain,
% 0.46/0.68      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X4 @ X3)
% 0.46/0.68          | (r2_hidden @ X4 @ X2)
% 0.46/0.68          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.68  thf('2', plain,
% 0.46/0.68      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.46/0.68         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['1'])).
% 0.46/0.68  thf('3', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_D_1 @ sk_E_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['0', '2'])).
% 0.46/0.68  thf(d10_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.68  thf('4', plain,
% 0.46/0.68      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.68  thf('5', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.46/0.68      inference('simplify', [status(thm)], ['4'])).
% 0.46/0.68  thf(t103_zfmisc_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ~( ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.46/0.68          ( r2_hidden @ D @ A ) & 
% 0.46/0.68          ( ![E:$i,F:$i]:
% 0.46/0.68            ( ~( ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) & 
% 0.46/0.68                 ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.46/0.68  thf('6', plain,
% 0.46/0.68      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.68         (~ (r1_tarski @ X16 @ (k2_zfmisc_1 @ X17 @ X18))
% 0.46/0.68          | ((X19)
% 0.46/0.68              = (k4_tarski @ (sk_E @ X19 @ X18 @ X17) @ 
% 0.46/0.68                 (sk_F @ X19 @ X18 @ X17)))
% 0.46/0.68          | ~ (r2_hidden @ X19 @ X16))),
% 0.46/0.68      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.46/0.68  thf('7', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.46/0.68          | ((X2) = (k4_tarski @ (sk_E @ X2 @ X0 @ X1) @ (sk_F @ X2 @ X0 @ X1))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      (((sk_A)
% 0.46/0.68         = (k4_tarski @ (sk_E @ sk_A @ sk_E_1 @ sk_D_1) @ 
% 0.46/0.68            (sk_F @ sk_A @ sk_E_1 @ sk_D_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['3', '7'])).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      ((r2_hidden @ sk_A @ 
% 0.46/0.68        (k3_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ 
% 0.46/0.68         (k2_zfmisc_1 @ sk_D_1 @ sk_E_1)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('10', plain,
% 0.46/0.68      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X4 @ X3)
% 0.46/0.68          | (r2_hidden @ X4 @ X1)
% 0.46/0.68          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.46/0.68         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['10'])).
% 0.46/0.68  thf('12', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.46/0.68      inference('sup-', [status(thm)], ['9', '11'])).
% 0.46/0.68  thf('13', plain,
% 0.46/0.68      (((sk_A)
% 0.46/0.68         = (k4_tarski @ (sk_E @ sk_A @ sk_E_1 @ sk_D_1) @ 
% 0.46/0.68            (sk_F @ sk_A @ sk_E_1 @ sk_D_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['3', '7'])).
% 0.46/0.68  thf(l54_zfmisc_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.46/0.68       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.68         ((r2_hidden @ X11 @ X12)
% 0.46/0.68          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 0.46/0.68      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.46/0.68          | (r2_hidden @ (sk_E @ sk_A @ sk_E_1 @ sk_D_1) @ X1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.68  thf('16', plain, ((r2_hidden @ (sk_E @ sk_A @ sk_E_1 @ sk_D_1) @ sk_B)),
% 0.46/0.68      inference('sup-', [status(thm)], ['12', '15'])).
% 0.46/0.68  thf('17', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_D_1 @ sk_E_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['0', '2'])).
% 0.46/0.68  thf('18', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.46/0.68      inference('simplify', [status(thm)], ['4'])).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.68         (~ (r1_tarski @ X16 @ (k2_zfmisc_1 @ X17 @ X18))
% 0.46/0.68          | (r2_hidden @ (sk_E @ X19 @ X18 @ X17) @ X17)
% 0.46/0.68          | ~ (r2_hidden @ X19 @ X16))),
% 0.46/0.68      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.46/0.68  thf('20', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.46/0.68          | (r2_hidden @ (sk_E @ X2 @ X0 @ X1) @ X1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.68  thf('21', plain, ((r2_hidden @ (sk_E @ sk_A @ sk_E_1 @ sk_D_1) @ sk_D_1)),
% 0.46/0.68      inference('sup-', [status(thm)], ['17', '20'])).
% 0.46/0.68  thf('22', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.68          | ~ (r2_hidden @ X0 @ X2)
% 0.46/0.68          | (r2_hidden @ X0 @ X3)
% 0.46/0.68          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.68  thf('23', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.46/0.68          | ~ (r2_hidden @ X0 @ X2)
% 0.46/0.68          | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.68      inference('simplify', [status(thm)], ['22'])).
% 0.46/0.68  thf('24', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (r2_hidden @ (sk_E @ sk_A @ sk_E_1 @ sk_D_1) @ X0)
% 0.46/0.68          | (r2_hidden @ (sk_E @ sk_A @ sk_E_1 @ sk_D_1) @ 
% 0.46/0.68             (k3_xboole_0 @ X0 @ sk_D_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['21', '23'])).
% 0.46/0.68  thf('25', plain,
% 0.46/0.68      ((r2_hidden @ (sk_E @ sk_A @ sk_E_1 @ sk_D_1) @ 
% 0.46/0.68        (k3_xboole_0 @ sk_B @ sk_D_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['16', '24'])).
% 0.46/0.68  thf('26', plain,
% 0.46/0.68      (![X20 : $i, X21 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X20 @ (k3_xboole_0 @ sk_B @ sk_D_1))
% 0.46/0.68          | ~ (r2_hidden @ X21 @ (k3_xboole_0 @ sk_C @ sk_E_1))
% 0.46/0.68          | ((sk_A) != (k4_tarski @ X20 @ X21)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('27', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((sk_A) != (k4_tarski @ (sk_E @ sk_A @ sk_E_1 @ sk_D_1) @ X0))
% 0.46/0.68          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_C @ sk_E_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.68  thf('28', plain,
% 0.46/0.68      ((((sk_A) != (sk_A))
% 0.46/0.68        | ~ (r2_hidden @ (sk_F @ sk_A @ sk_E_1 @ sk_D_1) @ 
% 0.46/0.68             (k3_xboole_0 @ sk_C @ sk_E_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['8', '27'])).
% 0.46/0.68  thf('29', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.46/0.68      inference('sup-', [status(thm)], ['9', '11'])).
% 0.46/0.68  thf('30', plain,
% 0.46/0.68      (((sk_A)
% 0.46/0.68         = (k4_tarski @ (sk_E @ sk_A @ sk_E_1 @ sk_D_1) @ 
% 0.46/0.68            (sk_F @ sk_A @ sk_E_1 @ sk_D_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['3', '7'])).
% 0.46/0.68  thf('31', plain,
% 0.46/0.68      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.68         ((r2_hidden @ X13 @ X14)
% 0.46/0.68          | ~ (r2_hidden @ (k4_tarski @ X11 @ X13) @ (k2_zfmisc_1 @ X12 @ X14)))),
% 0.46/0.68      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.46/0.68  thf('32', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.46/0.68          | (r2_hidden @ (sk_F @ sk_A @ sk_E_1 @ sk_D_1) @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.68  thf('33', plain, ((r2_hidden @ (sk_F @ sk_A @ sk_E_1 @ sk_D_1) @ sk_C)),
% 0.46/0.68      inference('sup-', [status(thm)], ['29', '32'])).
% 0.46/0.68  thf('34', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_D_1 @ sk_E_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['0', '2'])).
% 0.46/0.68  thf('35', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.46/0.68      inference('simplify', [status(thm)], ['4'])).
% 0.46/0.68  thf('36', plain,
% 0.46/0.68      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.68         (~ (r1_tarski @ X16 @ (k2_zfmisc_1 @ X17 @ X18))
% 0.46/0.68          | (r2_hidden @ (sk_F @ X19 @ X18 @ X17) @ X18)
% 0.46/0.68          | ~ (r2_hidden @ X19 @ X16))),
% 0.46/0.68      inference('cnf', [status(esa)], [t103_zfmisc_1])).
% 0.46/0.68  thf('37', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.46/0.68          | (r2_hidden @ (sk_F @ X2 @ X0 @ X1) @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.68  thf('38', plain, ((r2_hidden @ (sk_F @ sk_A @ sk_E_1 @ sk_D_1) @ sk_E_1)),
% 0.46/0.68      inference('sup-', [status(thm)], ['34', '37'])).
% 0.46/0.68  thf('39', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.46/0.68          | ~ (r2_hidden @ X0 @ X2)
% 0.46/0.68          | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.68      inference('simplify', [status(thm)], ['22'])).
% 0.46/0.68  thf('40', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (r2_hidden @ (sk_F @ sk_A @ sk_E_1 @ sk_D_1) @ X0)
% 0.46/0.68          | (r2_hidden @ (sk_F @ sk_A @ sk_E_1 @ sk_D_1) @ 
% 0.46/0.68             (k3_xboole_0 @ X0 @ sk_E_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.68  thf('41', plain,
% 0.46/0.68      ((r2_hidden @ (sk_F @ sk_A @ sk_E_1 @ sk_D_1) @ 
% 0.46/0.68        (k3_xboole_0 @ sk_C @ sk_E_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['33', '40'])).
% 0.46/0.68  thf('42', plain, (((sk_A) != (sk_A))),
% 0.46/0.68      inference('demod', [status(thm)], ['28', '41'])).
% 0.46/0.68  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.46/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
