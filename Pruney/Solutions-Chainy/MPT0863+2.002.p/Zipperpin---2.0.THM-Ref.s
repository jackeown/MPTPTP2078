%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Oj2BEiXKEp

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:58 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 116 expanded)
%              Number of leaves         :   21 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  559 (1231 expanded)
%              Number of equality atoms :   74 ( 174 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
     != sk_C_1 )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 )
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
     != sk_C_1 )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['4'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ ( k2_tarski @ X20 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k2_tarski @ sk_D_1 @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X28 ) @ X30 )
      | ~ ( r2_hidden @ X28 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('14',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_D_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X24: $i,X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X24 @ X26 ) @ X27 )
        = ( k2_tarski @ X24 @ X26 ) )
      | ( r2_hidden @ X26 @ X27 )
      | ( r2_hidden @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_E @ X0 )
      | ( r2_hidden @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_E @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( X12 = X9 )
      | ( X11
       != ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ ( k2_mcart_1 @ sk_A ) ) )
    | ( sk_E
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('25',plain,
    ( ( sk_E
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_D_1
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_E )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( ( sk_E != sk_E )
      | ( sk_D_1
        = ( k2_mcart_1 @ sk_A ) ) )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ sk_A ) )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('31',plain,
    ( ( sk_D_1 != sk_D_1 )
   <= ( ( ( k2_mcart_1 @ sk_A )
       != sk_E )
      & ( ( k2_mcart_1 @ sk_A )
       != sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_E )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D_1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_E ) ),
    inference(split,[status(esa)],['26'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('35',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) @ ( k2_tarski @ sk_D_1 @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X28 ) @ X29 )
      | ~ ( r2_hidden @ X28 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('37',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ sk_C_1 @ X0 )
      | ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('42',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ ( k1_mcart_1 @ sk_A ) ) )
    | ( sk_C_1
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12 = X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_tarski @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('44',plain,
    ( ( sk_C_1
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_B
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('46',plain,
    ( ( ( sk_C_1 != sk_C_1 )
      | ( sk_B
        = ( k1_mcart_1 @ sk_A ) ) )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B
      = ( k1_mcart_1 @ sk_A ) )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C_1 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('49',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k1_mcart_1 @ sk_A )
       != sk_C_1 )
      & ( ( k1_mcart_1 @ sk_A )
       != sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C_1 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','32','33','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.16/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Oj2BEiXKEp
% 0.16/0.36  % Computer   : n017.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 10:57:46 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.23/0.37  % Running in FO mode
% 0.69/0.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.92  % Solved by: fo/fo7.sh
% 0.69/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.92  % done 561 iterations in 0.447s
% 0.69/0.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.92  % SZS output start Refutation
% 0.69/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.92  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.69/0.92  thf(sk_E_type, type, sk_E: $i).
% 0.69/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.69/0.92  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.69/0.92  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.69/0.92  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.69/0.92  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.69/0.92  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.69/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.92  thf(t19_mcart_1, conjecture,
% 0.69/0.92    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.69/0.92     ( ( r2_hidden @
% 0.69/0.92         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) =>
% 0.69/0.92       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.69/0.92         ( ( ( k2_mcart_1 @ A ) = ( D ) ) | ( ( k2_mcart_1 @ A ) = ( E ) ) ) ) ))).
% 0.69/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.92    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.69/0.92        ( ( r2_hidden @
% 0.69/0.92            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k2_tarski @ D @ E ) ) ) =>
% 0.69/0.92          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.69/0.92            ( ( ( k2_mcart_1 @ A ) = ( D ) ) | ( ( k2_mcart_1 @ A ) = ( E ) ) ) ) ) )),
% 0.69/0.92    inference('cnf.neg', [status(esa)], [t19_mcart_1])).
% 0.69/0.92  thf('0', plain,
% 0.69/0.92      ((((k1_mcart_1 @ sk_A) != (sk_C_1)) | ((k2_mcart_1 @ sk_A) != (sk_E)))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('1', plain,
% 0.69/0.92      (~ (((k1_mcart_1 @ sk_A) = (sk_C_1))) | 
% 0.69/0.92       ~ (((k2_mcart_1 @ sk_A) = (sk_E)))),
% 0.69/0.92      inference('split', [status(esa)], ['0'])).
% 0.69/0.92  thf('2', plain,
% 0.69/0.92      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('3', plain,
% 0.69/0.92      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.69/0.92       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.69/0.92      inference('split', [status(esa)], ['2'])).
% 0.69/0.92  thf('4', plain,
% 0.69/0.92      ((((k1_mcart_1 @ sk_A) != (sk_C_1)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('5', plain,
% 0.69/0.92      (~ (((k1_mcart_1 @ sk_A) = (sk_C_1))) | 
% 0.69/0.92       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.69/0.92      inference('split', [status(esa)], ['4'])).
% 0.69/0.92  thf(t69_enumset1, axiom,
% 0.69/0.92    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.69/0.92  thf('6', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.69/0.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.69/0.92  thf(d10_xboole_0, axiom,
% 0.69/0.92    (![A:$i,B:$i]:
% 0.69/0.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.69/0.92  thf('7', plain,
% 0.69/0.92      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.69/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.69/0.92  thf('8', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.69/0.92      inference('simplify', [status(thm)], ['7'])).
% 0.69/0.92  thf(t38_zfmisc_1, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.69/0.92       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.69/0.92  thf('9', plain,
% 0.69/0.92      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.69/0.92         ((r2_hidden @ X20 @ X21)
% 0.69/0.92          | ~ (r1_tarski @ (k2_tarski @ X20 @ X22) @ X21))),
% 0.69/0.92      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.69/0.92  thf('10', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.69/0.92      inference('sup-', [status(thm)], ['8', '9'])).
% 0.69/0.92  thf('11', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['6', '10'])).
% 0.69/0.92  thf('12', plain,
% 0.69/0.92      ((r2_hidden @ sk_A @ 
% 0.69/0.92        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C_1) @ 
% 0.69/0.92         (k2_tarski @ sk_D_1 @ sk_E)))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf(t10_mcart_1, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.69/0.92       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.69/0.92         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.69/0.92  thf('13', plain,
% 0.69/0.92      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.69/0.92         ((r2_hidden @ (k2_mcart_1 @ X28) @ X30)
% 0.69/0.92          | ~ (r2_hidden @ X28 @ (k2_zfmisc_1 @ X29 @ X30)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.69/0.92  thf('14', plain,
% 0.69/0.92      ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k2_tarski @ sk_D_1 @ sk_E))),
% 0.69/0.92      inference('sup-', [status(thm)], ['12', '13'])).
% 0.69/0.92  thf(t72_zfmisc_1, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.69/0.92       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.69/0.92  thf('15', plain,
% 0.69/0.92      (![X24 : $i, X26 : $i, X27 : $i]:
% 0.69/0.92         (((k4_xboole_0 @ (k2_tarski @ X24 @ X26) @ X27)
% 0.69/0.92            = (k2_tarski @ X24 @ X26))
% 0.69/0.92          | (r2_hidden @ X26 @ X27)
% 0.69/0.92          | (r2_hidden @ X24 @ X27))),
% 0.69/0.92      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.69/0.92  thf(d5_xboole_0, axiom,
% 0.69/0.92    (![A:$i,B:$i,C:$i]:
% 0.69/0.92     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.69/0.92       ( ![D:$i]:
% 0.69/0.92         ( ( r2_hidden @ D @ C ) <=>
% 0.69/0.92           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.69/0.92  thf('16', plain,
% 0.69/0.92      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.69/0.92         (~ (r2_hidden @ X4 @ X3)
% 0.69/0.92          | ~ (r2_hidden @ X4 @ X2)
% 0.69/0.92          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.69/0.92      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.69/0.92  thf('17', plain,
% 0.69/0.92      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.69/0.92         (~ (r2_hidden @ X4 @ X2)
% 0.69/0.92          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.69/0.92      inference('simplify', [status(thm)], ['16'])).
% 0.69/0.92  thf('18', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.92         (~ (r2_hidden @ X3 @ (k2_tarski @ X1 @ X0))
% 0.69/0.92          | (r2_hidden @ X1 @ X2)
% 0.69/0.92          | (r2_hidden @ X0 @ X2)
% 0.69/0.92          | ~ (r2_hidden @ X3 @ X2))),
% 0.69/0.92      inference('sup-', [status(thm)], ['15', '17'])).
% 0.69/0.92  thf('19', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0)
% 0.69/0.92          | (r2_hidden @ sk_E @ X0)
% 0.69/0.92          | (r2_hidden @ sk_D_1 @ X0))),
% 0.69/0.92      inference('sup-', [status(thm)], ['14', '18'])).
% 0.69/0.92  thf('20', plain,
% 0.69/0.92      (((r2_hidden @ sk_D_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 0.69/0.92        | (r2_hidden @ sk_E @ (k1_tarski @ (k2_mcart_1 @ sk_A))))),
% 0.69/0.92      inference('sup-', [status(thm)], ['11', '19'])).
% 0.69/0.92  thf(d1_tarski, axiom,
% 0.69/0.92    (![A:$i,B:$i]:
% 0.69/0.92     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.69/0.92       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.69/0.92  thf('21', plain,
% 0.69/0.92      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.69/0.92         (~ (r2_hidden @ X12 @ X11)
% 0.69/0.92          | ((X12) = (X9))
% 0.69/0.92          | ((X11) != (k1_tarski @ X9)))),
% 0.69/0.92      inference('cnf', [status(esa)], [d1_tarski])).
% 0.69/0.92  thf('22', plain,
% 0.69/0.92      (![X9 : $i, X12 : $i]:
% 0.69/0.92         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 0.69/0.92      inference('simplify', [status(thm)], ['21'])).
% 0.69/0.92  thf('23', plain,
% 0.69/0.92      (((r2_hidden @ sk_D_1 @ (k1_tarski @ (k2_mcart_1 @ sk_A)))
% 0.69/0.92        | ((sk_E) = (k2_mcart_1 @ sk_A)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['20', '22'])).
% 0.69/0.92  thf('24', plain,
% 0.69/0.92      (![X9 : $i, X12 : $i]:
% 0.69/0.92         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 0.69/0.92      inference('simplify', [status(thm)], ['21'])).
% 0.69/0.92  thf('25', plain,
% 0.69/0.92      ((((sk_E) = (k2_mcart_1 @ sk_A)) | ((sk_D_1) = (k2_mcart_1 @ sk_A)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['23', '24'])).
% 0.69/0.92  thf('26', plain,
% 0.69/0.92      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_E)))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('27', plain,
% 0.69/0.92      ((((k2_mcart_1 @ sk_A) != (sk_E)))
% 0.69/0.92         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))))),
% 0.69/0.92      inference('split', [status(esa)], ['26'])).
% 0.69/0.92  thf('28', plain,
% 0.69/0.92      (((((sk_E) != (sk_E)) | ((sk_D_1) = (k2_mcart_1 @ sk_A))))
% 0.69/0.92         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))))),
% 0.69/0.92      inference('sup-', [status(thm)], ['25', '27'])).
% 0.69/0.92  thf('29', plain,
% 0.69/0.92      ((((sk_D_1) = (k2_mcart_1 @ sk_A)))
% 0.69/0.92         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))))),
% 0.69/0.92      inference('simplify', [status(thm)], ['28'])).
% 0.69/0.92  thf('30', plain,
% 0.69/0.92      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 0.69/0.92         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.69/0.92      inference('split', [status(esa)], ['2'])).
% 0.69/0.92  thf('31', plain,
% 0.69/0.92      ((((sk_D_1) != (sk_D_1)))
% 0.69/0.92         <= (~ (((k2_mcart_1 @ sk_A) = (sk_E))) & 
% 0.69/0.92             ~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.69/0.92      inference('sup-', [status(thm)], ['29', '30'])).
% 0.69/0.92  thf('32', plain,
% 0.69/0.92      ((((k2_mcart_1 @ sk_A) = (sk_E))) | (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.69/0.92      inference('simplify', [status(thm)], ['31'])).
% 0.69/0.92  thf('33', plain,
% 0.69/0.92      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_E)))),
% 0.69/0.92      inference('split', [status(esa)], ['26'])).
% 0.69/0.92  thf('34', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.69/0.92      inference('sup+', [status(thm)], ['6', '10'])).
% 0.69/0.92  thf('35', plain,
% 0.69/0.92      ((r2_hidden @ sk_A @ 
% 0.69/0.92        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C_1) @ 
% 0.69/0.92         (k2_tarski @ sk_D_1 @ sk_E)))),
% 0.69/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.92  thf('36', plain,
% 0.69/0.92      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.69/0.92         ((r2_hidden @ (k1_mcart_1 @ X28) @ X29)
% 0.69/0.92          | ~ (r2_hidden @ X28 @ (k2_zfmisc_1 @ X29 @ X30)))),
% 0.69/0.92      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.69/0.92  thf('37', plain,
% 0.69/0.92      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C_1))),
% 0.69/0.92      inference('sup-', [status(thm)], ['35', '36'])).
% 0.69/0.92  thf('38', plain,
% 0.69/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.69/0.92         (~ (r2_hidden @ X3 @ (k2_tarski @ X1 @ X0))
% 0.69/0.92          | (r2_hidden @ X1 @ X2)
% 0.69/0.92          | (r2_hidden @ X0 @ X2)
% 0.69/0.92          | ~ (r2_hidden @ X3 @ X2))),
% 0.69/0.92      inference('sup-', [status(thm)], ['15', '17'])).
% 0.69/0.92  thf('39', plain,
% 0.69/0.92      (![X0 : $i]:
% 0.69/0.92         (~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0)
% 0.69/0.92          | (r2_hidden @ sk_C_1 @ X0)
% 0.69/0.92          | (r2_hidden @ sk_B @ X0))),
% 0.69/0.92      inference('sup-', [status(thm)], ['37', '38'])).
% 0.69/0.92  thf('40', plain,
% 0.69/0.92      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.69/0.92        | (r2_hidden @ sk_C_1 @ (k1_tarski @ (k1_mcart_1 @ sk_A))))),
% 0.69/0.92      inference('sup-', [status(thm)], ['34', '39'])).
% 0.69/0.92  thf('41', plain,
% 0.69/0.92      (![X9 : $i, X12 : $i]:
% 0.69/0.92         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 0.69/0.92      inference('simplify', [status(thm)], ['21'])).
% 0.69/0.92  thf('42', plain,
% 0.69/0.92      (((r2_hidden @ sk_B @ (k1_tarski @ (k1_mcart_1 @ sk_A)))
% 0.69/0.92        | ((sk_C_1) = (k1_mcart_1 @ sk_A)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['40', '41'])).
% 0.69/0.92  thf('43', plain,
% 0.69/0.92      (![X9 : $i, X12 : $i]:
% 0.69/0.92         (((X12) = (X9)) | ~ (r2_hidden @ X12 @ (k1_tarski @ X9)))),
% 0.69/0.92      inference('simplify', [status(thm)], ['21'])).
% 0.69/0.92  thf('44', plain,
% 0.69/0.92      ((((sk_C_1) = (k1_mcart_1 @ sk_A)) | ((sk_B) = (k1_mcart_1 @ sk_A)))),
% 0.69/0.92      inference('sup-', [status(thm)], ['42', '43'])).
% 0.69/0.92  thf('45', plain,
% 0.69/0.92      ((((k1_mcart_1 @ sk_A) != (sk_C_1)))
% 0.69/0.92         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.69/0.92      inference('split', [status(esa)], ['4'])).
% 0.69/0.92  thf('46', plain,
% 0.69/0.92      (((((sk_C_1) != (sk_C_1)) | ((sk_B) = (k1_mcart_1 @ sk_A))))
% 0.69/0.92         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.69/0.92      inference('sup-', [status(thm)], ['44', '45'])).
% 0.69/0.92  thf('47', plain,
% 0.69/0.92      ((((sk_B) = (k1_mcart_1 @ sk_A)))
% 0.69/0.92         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C_1))))),
% 0.69/0.92      inference('simplify', [status(thm)], ['46'])).
% 0.69/0.92  thf('48', plain,
% 0.69/0.92      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.69/0.92         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.69/0.92      inference('split', [status(esa)], ['2'])).
% 0.69/0.92  thf('49', plain,
% 0.69/0.92      ((((sk_B) != (sk_B)))
% 0.69/0.92         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C_1))) & 
% 0.69/0.92             ~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.69/0.92      inference('sup-', [status(thm)], ['47', '48'])).
% 0.69/0.92  thf('50', plain,
% 0.69/0.92      ((((k1_mcart_1 @ sk_A) = (sk_B))) | (((k1_mcart_1 @ sk_A) = (sk_C_1)))),
% 0.69/0.92      inference('simplify', [status(thm)], ['49'])).
% 0.69/0.92  thf('51', plain, ($false),
% 0.69/0.92      inference('sat_resolution*', [status(thm)],
% 0.69/0.92                ['1', '3', '5', '32', '33', '50'])).
% 0.69/0.92  
% 0.69/0.92  % SZS output end Refutation
% 0.69/0.92  
% 0.69/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
