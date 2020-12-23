%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fKjOqsAlkS

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:58 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
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

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

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
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_D_3 @ sk_E_2 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('2',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_D_3 @ sk_E_2 ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X29 @ X26 @ X27 ) @ ( sk_E_1 @ X29 @ X26 @ X27 ) @ X29 @ X26 @ X27 )
      | ( X28
       != ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X26: $i,X27: $i,X29: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X29 @ X26 @ X27 ) @ ( sk_E_1 @ X29 @ X26 @ X27 ) @ X29 @ X26 @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ sk_A @ sk_E_2 @ sk_D_3 ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19
        = ( k4_tarski @ X17 @ X18 ) )
      | ~ ( zip_tseitin_0 @ X18 @ X17 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_D_3 @ sk_E_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('11',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('14',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X33 @ X34 )
      | ~ ( r2_hidden @ ( k4_tarski @ X33 @ X35 ) @ ( k2_zfmisc_1 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ sk_B ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ sk_A @ sk_E_2 @ sk_D_3 ),
    inference('sup-',[status(thm)],['3','5'])).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X17 @ X21 )
      | ~ ( zip_tseitin_0 @ X18 @ X17 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ sk_D_3 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ X0 )
      | ( r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ ( k3_xboole_0 @ X0 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ ( k3_xboole_0 @ sk_B @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X40 @ ( k3_xboole_0 @ sk_B @ sk_D_3 ) )
      | ~ ( r2_hidden @ X41 @ ( k3_xboole_0 @ sk_C_1 @ sk_E_2 ) )
      | ( sk_A
       != ( k4_tarski @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_C_1 @ sk_E_2 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ ( k3_xboole_0 @ sk_C_1 @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['8','25'])).

thf('27',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('28',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('29',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X35 @ X36 )
      | ~ ( r2_hidden @ ( k4_tarski @ X33 @ X35 ) @ ( k2_zfmisc_1 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ sk_A @ sk_E_2 @ sk_D_3 ),
    inference('sup-',[status(thm)],['3','5'])).

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( r2_hidden @ X18 @ X20 )
      | ~ ( zip_tseitin_0 @ X18 @ X17 @ X19 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ sk_E_2 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ X0 )
      | ( r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ ( k3_xboole_0 @ X0 @ sk_E_2 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3 ) @ ( k3_xboole_0 @ sk_C_1 @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['26','37'])).

thf('39',plain,(
    $false ),
    inference(simplify,[status(thm)],['38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fKjOqsAlkS
% 0.14/0.37  % Computer   : n002.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 13:32:07 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 1.02/1.22  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.02/1.22  % Solved by: fo/fo7.sh
% 1.02/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.22  % done 1065 iterations in 0.755s
% 1.02/1.22  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.02/1.22  % SZS output start Refutation
% 1.02/1.22  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.02/1.22  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.02/1.22  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.02/1.22  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 1.02/1.22  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.22  thf(sk_D_3_type, type, sk_D_3: $i).
% 1.02/1.22  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 1.02/1.22  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.02/1.22  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 1.02/1.22  thf(sk_E_2_type, type, sk_E_2: $i).
% 1.02/1.22  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.02/1.22  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.22  thf(t104_zfmisc_1, conjecture,
% 1.02/1.22    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.02/1.22     ( ~( ( r2_hidden @
% 1.02/1.22            A @ 
% 1.02/1.22            ( k3_xboole_0 @ ( k2_zfmisc_1 @ B @ C ) @ ( k2_zfmisc_1 @ D @ E ) ) ) & 
% 1.02/1.22          ( ![F:$i,G:$i]:
% 1.02/1.22            ( ~( ( ( A ) = ( k4_tarski @ F @ G ) ) & 
% 1.02/1.22                 ( r2_hidden @ F @ ( k3_xboole_0 @ B @ D ) ) & 
% 1.02/1.22                 ( r2_hidden @ G @ ( k3_xboole_0 @ C @ E ) ) ) ) ) ) ))).
% 1.02/1.22  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.22    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 1.02/1.22        ( ~( ( r2_hidden @
% 1.02/1.22               A @ 
% 1.02/1.22               ( k3_xboole_0 @
% 1.02/1.22                 ( k2_zfmisc_1 @ B @ C ) @ ( k2_zfmisc_1 @ D @ E ) ) ) & 
% 1.02/1.22             ( ![F:$i,G:$i]:
% 1.02/1.22               ( ~( ( ( A ) = ( k4_tarski @ F @ G ) ) & 
% 1.02/1.22                    ( r2_hidden @ F @ ( k3_xboole_0 @ B @ D ) ) & 
% 1.02/1.22                    ( r2_hidden @ G @ ( k3_xboole_0 @ C @ E ) ) ) ) ) ) ) )),
% 1.02/1.22    inference('cnf.neg', [status(esa)], [t104_zfmisc_1])).
% 1.02/1.22  thf('0', plain,
% 1.02/1.22      ((r2_hidden @ sk_A @ 
% 1.02/1.22        (k3_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C_1) @ 
% 1.02/1.22         (k2_zfmisc_1 @ sk_D_3 @ sk_E_2)))),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.22  thf(d4_xboole_0, axiom,
% 1.02/1.22    (![A:$i,B:$i,C:$i]:
% 1.02/1.22     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.02/1.22       ( ![D:$i]:
% 1.02/1.22         ( ( r2_hidden @ D @ C ) <=>
% 1.02/1.22           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.02/1.22  thf('1', plain,
% 1.02/1.22      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.02/1.22         (~ (r2_hidden @ X10 @ X9)
% 1.02/1.22          | (r2_hidden @ X10 @ X8)
% 1.02/1.22          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 1.02/1.22      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.02/1.22  thf('2', plain,
% 1.02/1.22      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.02/1.22         ((r2_hidden @ X10 @ X8)
% 1.02/1.22          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 1.02/1.22      inference('simplify', [status(thm)], ['1'])).
% 1.02/1.22  thf('3', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_D_3 @ sk_E_2))),
% 1.02/1.22      inference('sup-', [status(thm)], ['0', '2'])).
% 1.02/1.22  thf(d2_zfmisc_1, axiom,
% 1.02/1.22    (![A:$i,B:$i,C:$i]:
% 1.02/1.22     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 1.02/1.22       ( ![D:$i]:
% 1.02/1.22         ( ( r2_hidden @ D @ C ) <=>
% 1.02/1.22           ( ?[E:$i,F:$i]:
% 1.02/1.22             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 1.02/1.22               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 1.02/1.22  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 1.02/1.22  thf(zf_stmt_2, axiom,
% 1.02/1.22    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 1.02/1.22     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 1.02/1.22       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 1.02/1.22         ( r2_hidden @ E @ A ) ) ))).
% 1.02/1.22  thf(zf_stmt_3, axiom,
% 1.02/1.22    (![A:$i,B:$i,C:$i]:
% 1.02/1.22     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 1.02/1.22       ( ![D:$i]:
% 1.02/1.22         ( ( r2_hidden @ D @ C ) <=>
% 1.02/1.22           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 1.02/1.22  thf('4', plain,
% 1.02/1.22      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.02/1.22         (~ (r2_hidden @ X29 @ X28)
% 1.02/1.22          | (zip_tseitin_0 @ (sk_F_1 @ X29 @ X26 @ X27) @ 
% 1.02/1.22             (sk_E_1 @ X29 @ X26 @ X27) @ X29 @ X26 @ X27)
% 1.02/1.22          | ((X28) != (k2_zfmisc_1 @ X27 @ X26)))),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.02/1.22  thf('5', plain,
% 1.02/1.22      (![X26 : $i, X27 : $i, X29 : $i]:
% 1.02/1.22         ((zip_tseitin_0 @ (sk_F_1 @ X29 @ X26 @ X27) @ 
% 1.02/1.22           (sk_E_1 @ X29 @ X26 @ X27) @ X29 @ X26 @ X27)
% 1.02/1.22          | ~ (r2_hidden @ X29 @ (k2_zfmisc_1 @ X27 @ X26)))),
% 1.02/1.22      inference('simplify', [status(thm)], ['4'])).
% 1.02/1.22  thf('6', plain,
% 1.02/1.22      ((zip_tseitin_0 @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3) @ 
% 1.02/1.22        (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3) @ sk_A @ sk_E_2 @ sk_D_3)),
% 1.02/1.22      inference('sup-', [status(thm)], ['3', '5'])).
% 1.02/1.22  thf('7', plain,
% 1.02/1.22      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.02/1.22         (((X19) = (k4_tarski @ X17 @ X18))
% 1.02/1.22          | ~ (zip_tseitin_0 @ X18 @ X17 @ X19 @ X20 @ X21))),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.02/1.22  thf('8', plain,
% 1.02/1.22      (((sk_A)
% 1.02/1.22         = (k4_tarski @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3) @ 
% 1.02/1.22            (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3)))),
% 1.02/1.22      inference('sup-', [status(thm)], ['6', '7'])).
% 1.02/1.22  thf('9', plain,
% 1.02/1.22      ((r2_hidden @ sk_A @ 
% 1.02/1.22        (k3_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C_1) @ 
% 1.02/1.22         (k2_zfmisc_1 @ sk_D_3 @ sk_E_2)))),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.22  thf('10', plain,
% 1.02/1.22      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.02/1.22         (~ (r2_hidden @ X10 @ X9)
% 1.02/1.22          | (r2_hidden @ X10 @ X7)
% 1.02/1.22          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 1.02/1.22      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.02/1.22  thf('11', plain,
% 1.02/1.22      (![X7 : $i, X8 : $i, X10 : $i]:
% 1.02/1.22         ((r2_hidden @ X10 @ X7)
% 1.02/1.22          | ~ (r2_hidden @ X10 @ (k3_xboole_0 @ X7 @ X8)))),
% 1.02/1.22      inference('simplify', [status(thm)], ['10'])).
% 1.02/1.22  thf('12', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 1.02/1.22      inference('sup-', [status(thm)], ['9', '11'])).
% 1.02/1.22  thf('13', plain,
% 1.02/1.22      (((sk_A)
% 1.02/1.22         = (k4_tarski @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3) @ 
% 1.02/1.22            (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3)))),
% 1.02/1.22      inference('sup-', [status(thm)], ['6', '7'])).
% 1.02/1.22  thf(l54_zfmisc_1, axiom,
% 1.02/1.22    (![A:$i,B:$i,C:$i,D:$i]:
% 1.02/1.22     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 1.02/1.22       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 1.02/1.22  thf('14', plain,
% 1.02/1.22      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.02/1.22         ((r2_hidden @ X33 @ X34)
% 1.02/1.22          | ~ (r2_hidden @ (k4_tarski @ X33 @ X35) @ (k2_zfmisc_1 @ X34 @ X36)))),
% 1.02/1.22      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.02/1.22  thf('15', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 1.02/1.22          | (r2_hidden @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3) @ X1))),
% 1.02/1.22      inference('sup-', [status(thm)], ['13', '14'])).
% 1.02/1.22  thf('16', plain, ((r2_hidden @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3) @ sk_B)),
% 1.02/1.22      inference('sup-', [status(thm)], ['12', '15'])).
% 1.02/1.22  thf('17', plain,
% 1.02/1.22      ((zip_tseitin_0 @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3) @ 
% 1.02/1.22        (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3) @ sk_A @ sk_E_2 @ sk_D_3)),
% 1.02/1.22      inference('sup-', [status(thm)], ['3', '5'])).
% 1.02/1.22  thf('18', plain,
% 1.02/1.22      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.02/1.22         ((r2_hidden @ X17 @ X21)
% 1.02/1.22          | ~ (zip_tseitin_0 @ X18 @ X17 @ X19 @ X20 @ X21))),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.02/1.22  thf('19', plain, ((r2_hidden @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3) @ sk_D_3)),
% 1.02/1.22      inference('sup-', [status(thm)], ['17', '18'])).
% 1.02/1.22  thf('20', plain,
% 1.02/1.22      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.02/1.22         (~ (r2_hidden @ X6 @ X7)
% 1.02/1.22          | ~ (r2_hidden @ X6 @ X8)
% 1.02/1.22          | (r2_hidden @ X6 @ X9)
% 1.02/1.22          | ((X9) != (k3_xboole_0 @ X7 @ X8)))),
% 1.02/1.22      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.02/1.22  thf('21', plain,
% 1.02/1.22      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.02/1.22         ((r2_hidden @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 1.02/1.22          | ~ (r2_hidden @ X6 @ X8)
% 1.02/1.22          | ~ (r2_hidden @ X6 @ X7))),
% 1.02/1.22      inference('simplify', [status(thm)], ['20'])).
% 1.02/1.22  thf('22', plain,
% 1.02/1.22      (![X0 : $i]:
% 1.02/1.22         (~ (r2_hidden @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3) @ X0)
% 1.02/1.22          | (r2_hidden @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3) @ 
% 1.02/1.22             (k3_xboole_0 @ X0 @ sk_D_3)))),
% 1.02/1.22      inference('sup-', [status(thm)], ['19', '21'])).
% 1.02/1.22  thf('23', plain,
% 1.02/1.22      ((r2_hidden @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3) @ 
% 1.02/1.22        (k3_xboole_0 @ sk_B @ sk_D_3))),
% 1.02/1.22      inference('sup-', [status(thm)], ['16', '22'])).
% 1.02/1.22  thf('24', plain,
% 1.02/1.22      (![X40 : $i, X41 : $i]:
% 1.02/1.22         (~ (r2_hidden @ X40 @ (k3_xboole_0 @ sk_B @ sk_D_3))
% 1.02/1.22          | ~ (r2_hidden @ X41 @ (k3_xboole_0 @ sk_C_1 @ sk_E_2))
% 1.02/1.22          | ((sk_A) != (k4_tarski @ X40 @ X41)))),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.22  thf('25', plain,
% 1.02/1.22      (![X0 : $i]:
% 1.02/1.22         (((sk_A) != (k4_tarski @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3) @ X0))
% 1.02/1.22          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_C_1 @ sk_E_2)))),
% 1.02/1.22      inference('sup-', [status(thm)], ['23', '24'])).
% 1.02/1.22  thf('26', plain,
% 1.02/1.22      ((((sk_A) != (sk_A))
% 1.02/1.22        | ~ (r2_hidden @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3) @ 
% 1.02/1.22             (k3_xboole_0 @ sk_C_1 @ sk_E_2)))),
% 1.02/1.22      inference('sup-', [status(thm)], ['8', '25'])).
% 1.02/1.22  thf('27', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 1.02/1.22      inference('sup-', [status(thm)], ['9', '11'])).
% 1.02/1.22  thf('28', plain,
% 1.02/1.22      (((sk_A)
% 1.02/1.22         = (k4_tarski @ (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3) @ 
% 1.02/1.22            (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3)))),
% 1.02/1.22      inference('sup-', [status(thm)], ['6', '7'])).
% 1.02/1.22  thf('29', plain,
% 1.02/1.22      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.02/1.22         ((r2_hidden @ X35 @ X36)
% 1.02/1.22          | ~ (r2_hidden @ (k4_tarski @ X33 @ X35) @ (k2_zfmisc_1 @ X34 @ X36)))),
% 1.02/1.22      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 1.02/1.22  thf('30', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 1.02/1.22          | (r2_hidden @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3) @ X0))),
% 1.02/1.22      inference('sup-', [status(thm)], ['28', '29'])).
% 1.02/1.22  thf('31', plain, ((r2_hidden @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3) @ sk_C_1)),
% 1.02/1.22      inference('sup-', [status(thm)], ['27', '30'])).
% 1.02/1.22  thf('32', plain,
% 1.02/1.22      ((zip_tseitin_0 @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3) @ 
% 1.02/1.22        (sk_E_1 @ sk_A @ sk_E_2 @ sk_D_3) @ sk_A @ sk_E_2 @ sk_D_3)),
% 1.02/1.22      inference('sup-', [status(thm)], ['3', '5'])).
% 1.02/1.22  thf('33', plain,
% 1.02/1.22      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.02/1.22         ((r2_hidden @ X18 @ X20)
% 1.02/1.22          | ~ (zip_tseitin_0 @ X18 @ X17 @ X19 @ X20 @ X21))),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.02/1.22  thf('34', plain, ((r2_hidden @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3) @ sk_E_2)),
% 1.02/1.22      inference('sup-', [status(thm)], ['32', '33'])).
% 1.02/1.22  thf('35', plain,
% 1.02/1.22      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.02/1.22         ((r2_hidden @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 1.02/1.22          | ~ (r2_hidden @ X6 @ X8)
% 1.02/1.22          | ~ (r2_hidden @ X6 @ X7))),
% 1.02/1.22      inference('simplify', [status(thm)], ['20'])).
% 1.02/1.22  thf('36', plain,
% 1.02/1.22      (![X0 : $i]:
% 1.02/1.22         (~ (r2_hidden @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3) @ X0)
% 1.02/1.22          | (r2_hidden @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3) @ 
% 1.02/1.22             (k3_xboole_0 @ X0 @ sk_E_2)))),
% 1.02/1.22      inference('sup-', [status(thm)], ['34', '35'])).
% 1.02/1.22  thf('37', plain,
% 1.02/1.22      ((r2_hidden @ (sk_F_1 @ sk_A @ sk_E_2 @ sk_D_3) @ 
% 1.02/1.22        (k3_xboole_0 @ sk_C_1 @ sk_E_2))),
% 1.02/1.22      inference('sup-', [status(thm)], ['31', '36'])).
% 1.02/1.22  thf('38', plain, (((sk_A) != (sk_A))),
% 1.02/1.22      inference('demod', [status(thm)], ['26', '37'])).
% 1.02/1.22  thf('39', plain, ($false), inference('simplify', [status(thm)], ['38'])).
% 1.02/1.22  
% 1.02/1.22  % SZS output end Refutation
% 1.02/1.22  
% 1.06/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
