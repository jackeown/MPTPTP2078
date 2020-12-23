%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mU7RNL6cNK

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:58 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 123 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  520 (1473 expanded)
%              Number of equality atoms :   19 (  61 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

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
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ sk_D_2 @ sk_E_2 ) ) ),
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
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_D_2 @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['0','2'])).

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

thf('4',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X20 @ X17 @ X18 ) @ ( sk_E_1 @ X20 @ X17 @ X18 ) @ X20 @ X17 @ X18 )
      | ( X19
       != ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X20 @ X17 @ X18 ) @ ( sk_E_1 @ X20 @ X17 @ X18 ) @ X20 @ X17 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ sk_A @ sk_E_2 @ sk_D_2 ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10
        = ( k4_tarski @ X8 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ sk_D_2 @ sk_E_2 ) ) ),
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
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X24 @ X25 )
      | ~ ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ ( k2_zfmisc_1 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ sk_A @ sk_E_2 @ sk_D_2 ),
    inference('sup-',[status(thm)],['3','5'])).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X8 @ X12 )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ sk_D_2 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ X0 )
      | ( r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ ( k3_xboole_0 @ X0 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ ( k3_xboole_0 @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k3_xboole_0 @ sk_B @ sk_D_2 ) )
      | ~ ( r2_hidden @ X30 @ ( k3_xboole_0 @ sk_C @ sk_E_2 ) )
      | ( sk_A
       != ( k4_tarski @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_C @ sk_E_2 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ ( k3_xboole_0 @ sk_C @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['8','25'])).

thf('27',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('28',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('29',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ X27 )
      | ~ ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ ( k2_zfmisc_1 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ sk_C ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ sk_A @ sk_E_2 @ sk_D_2 ),
    inference('sup-',[status(thm)],['3','5'])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ X11 )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ sk_E_2 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ X0 )
      | ( r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ ( k3_xboole_0 @ X0 @ sk_E_2 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ ( k3_xboole_0 @ sk_C @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['26','37'])).

thf('39',plain,(
    $false ),
    inference(simplify,[status(thm)],['38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mU7RNL6cNK
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:53:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 308 iterations in 0.197s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.65  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.46/0.65  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.46/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.46/0.65  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.65  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.46/0.65  thf(t104_zfmisc_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.46/0.65     ( ~( ( r2_hidden @
% 0.46/0.65            A @ 
% 0.46/0.65            ( k3_xboole_0 @ ( k2_zfmisc_1 @ B @ C ) @ ( k2_zfmisc_1 @ D @ E ) ) ) & 
% 0.46/0.65          ( ![F:$i,G:$i]:
% 0.46/0.65            ( ~( ( ( A ) = ( k4_tarski @ F @ G ) ) & 
% 0.46/0.65                 ( r2_hidden @ F @ ( k3_xboole_0 @ B @ D ) ) & 
% 0.46/0.65                 ( r2_hidden @ G @ ( k3_xboole_0 @ C @ E ) ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.46/0.65        ( ~( ( r2_hidden @
% 0.46/0.65               A @ 
% 0.46/0.65               ( k3_xboole_0 @
% 0.46/0.65                 ( k2_zfmisc_1 @ B @ C ) @ ( k2_zfmisc_1 @ D @ E ) ) ) & 
% 0.46/0.65             ( ![F:$i,G:$i]:
% 0.46/0.65               ( ~( ( ( A ) = ( k4_tarski @ F @ G ) ) & 
% 0.46/0.65                    ( r2_hidden @ F @ ( k3_xboole_0 @ B @ D ) ) & 
% 0.46/0.65                    ( r2_hidden @ G @ ( k3_xboole_0 @ C @ E ) ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t104_zfmisc_1])).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      ((r2_hidden @ sk_A @ 
% 0.46/0.65        (k3_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ 
% 0.46/0.65         (k2_zfmisc_1 @ sk_D_2 @ sk_E_2)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(d4_xboole_0, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.46/0.65       ( ![D:$i]:
% 0.46/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.65           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X4 @ X3)
% 0.46/0.65          | (r2_hidden @ X4 @ X2)
% 0.46/0.65          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.46/0.65         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['1'])).
% 0.46/0.65  thf('3', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_D_2 @ sk_E_2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['0', '2'])).
% 0.46/0.65  thf(d2_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.46/0.65       ( ![D:$i]:
% 0.46/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.65           ( ?[E:$i,F:$i]:
% 0.46/0.65             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.46/0.65               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.46/0.65  thf(zf_stmt_2, axiom,
% 0.46/0.65    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.46/0.65     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.46/0.65       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.46/0.65         ( r2_hidden @ E @ A ) ) ))).
% 0.46/0.65  thf(zf_stmt_3, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.46/0.65       ( ![D:$i]:
% 0.46/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.65           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X20 @ X19)
% 0.46/0.65          | (zip_tseitin_0 @ (sk_F_1 @ X20 @ X17 @ X18) @ 
% 0.46/0.65             (sk_E_1 @ X20 @ X17 @ X18) @ X20 @ X17 @ X18)
% 0.46/0.65          | ((X19) != (k2_zfmisc_1 @ X18 @ X17)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.46/0.65         ((zip_tseitin_0 @ (sk_F_1 @ X20 @ X17 @ X18) @ 
% 0.46/0.65           (sk_E_1 @ X20 @ X17 @ X18) @ X20 @ X17 @ X18)
% 0.46/0.65          | ~ (r2_hidden @ X20 @ (k2_zfmisc_1 @ X18 @ X17)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['4'])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      ((zip_tseitin_0 @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2) @ 
% 0.46/0.65        (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2) @ sk_A @ sk_E_2 @ sk_D_2)),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '5'])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.65         (((X10) = (k4_tarski @ X8 @ X9))
% 0.46/0.65          | ~ (zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (((sk_A)
% 0.46/0.65         = (k4_tarski @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2) @ 
% 0.46/0.65            (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      ((r2_hidden @ sk_A @ 
% 0.46/0.65        (k3_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C) @ 
% 0.46/0.65         (k2_zfmisc_1 @ sk_D_2 @ sk_E_2)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X4 @ X3)
% 0.46/0.65          | (r2_hidden @ X4 @ X1)
% 0.46/0.65          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.46/0.65         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['10'])).
% 0.46/0.65  thf('12', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['9', '11'])).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      (((sk_A)
% 0.46/0.65         = (k4_tarski @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2) @ 
% 0.46/0.65            (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf(l54_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.65     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.46/0.65       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.65         ((r2_hidden @ X24 @ X25)
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ (k2_zfmisc_1 @ X25 @ X27)))),
% 0.46/0.65      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.46/0.65          | (r2_hidden @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2) @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.65  thf('16', plain, ((r2_hidden @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2) @ sk_B)),
% 0.46/0.65      inference('sup-', [status(thm)], ['12', '15'])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      ((zip_tseitin_0 @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2) @ 
% 0.46/0.65        (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2) @ sk_A @ sk_E_2 @ sk_D_2)),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '5'])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.65         ((r2_hidden @ X8 @ X12)
% 0.46/0.65          | ~ (zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.65  thf('19', plain, ((r2_hidden @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2) @ sk_D_2)),
% 0.46/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.65          | ~ (r2_hidden @ X0 @ X2)
% 0.46/0.65          | (r2_hidden @ X0 @ X3)
% 0.46/0.65          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.46/0.65          | ~ (r2_hidden @ X0 @ X2)
% 0.46/0.65          | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.65      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r2_hidden @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2) @ X0)
% 0.46/0.65          | (r2_hidden @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2) @ 
% 0.46/0.65             (k3_xboole_0 @ X0 @ sk_D_2)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['19', '21'])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      ((r2_hidden @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2) @ 
% 0.46/0.65        (k3_xboole_0 @ sk_B @ sk_D_2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['16', '22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X29 : $i, X30 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X29 @ (k3_xboole_0 @ sk_B @ sk_D_2))
% 0.46/0.65          | ~ (r2_hidden @ X30 @ (k3_xboole_0 @ sk_C @ sk_E_2))
% 0.46/0.65          | ((sk_A) != (k4_tarski @ X29 @ X30)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((sk_A) != (k4_tarski @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2) @ X0))
% 0.46/0.65          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_C @ sk_E_2)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      ((((sk_A) != (sk_A))
% 0.46/0.65        | ~ (r2_hidden @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2) @ 
% 0.46/0.65             (k3_xboole_0 @ sk_C @ sk_E_2)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['8', '25'])).
% 0.46/0.65  thf('27', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['9', '11'])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (((sk_A)
% 0.46/0.65         = (k4_tarski @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2) @ 
% 0.46/0.65            (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.65         ((r2_hidden @ X26 @ X27)
% 0.46/0.65          | ~ (r2_hidden @ (k4_tarski @ X24 @ X26) @ (k2_zfmisc_1 @ X25 @ X27)))),
% 0.46/0.65      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.46/0.65          | (r2_hidden @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.65  thf('31', plain, ((r2_hidden @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2) @ sk_C)),
% 0.46/0.65      inference('sup-', [status(thm)], ['27', '30'])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      ((zip_tseitin_0 @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2) @ 
% 0.46/0.65        (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2) @ sk_A @ sk_E_2 @ sk_D_2)),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '5'])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.65         ((r2_hidden @ X9 @ X11)
% 0.46/0.65          | ~ (zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.65  thf('34', plain, ((r2_hidden @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2) @ sk_E_2)),
% 0.46/0.65      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.46/0.65          | ~ (r2_hidden @ X0 @ X2)
% 0.46/0.65          | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.65      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r2_hidden @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2) @ X0)
% 0.46/0.65          | (r2_hidden @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2) @ 
% 0.46/0.65             (k3_xboole_0 @ X0 @ sk_E_2)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      ((r2_hidden @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2) @ 
% 0.46/0.65        (k3_xboole_0 @ sk_C @ sk_E_2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['31', '36'])).
% 0.46/0.65  thf('38', plain, (((sk_A) != (sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['26', '37'])).
% 0.46/0.65  thf('39', plain, ($false), inference('simplify', [status(thm)], ['38'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
