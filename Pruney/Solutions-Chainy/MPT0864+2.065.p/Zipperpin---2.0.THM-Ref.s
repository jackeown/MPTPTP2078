%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qaknUTwstB

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:08 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 172 expanded)
%              Number of leaves         :   24 (  59 expanded)
%              Depth                    :   16
%              Number of atoms          :  540 (1416 expanded)
%              Number of equality atoms :   90 ( 247 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t20_mcart_1,conjecture,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ? [B: $i,C: $i] :
            ( A
            = ( k4_tarski @ B @ C ) )
       => ( ( A
           != ( k1_mcart_1 @ A ) )
          & ( A
           != ( k2_mcart_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_mcart_1])).

thf('0',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('1',plain,(
    ! [X38: $i,X40: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X38 @ X40 ) )
      = X40 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('2',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_C_1 ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A = sk_C_1 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_B @ sk_A ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X20 ) )
      = ( k1_tarski @ ( k4_tarski @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t42_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ ( k2_tarski @ X21 @ X24 ) )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t42_zfmisc_1])).

thf('14',plain,(
    ! [X21: $i,X24: $i] :
      ( r1_tarski @ ( k1_tarski @ X21 ) @ ( k2_tarski @ X21 @ X24 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t63_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
     => ( r2_hidden @ A @ C ) ) )).

thf('19',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X28 @ X30 ) @ X29 )
       != ( k2_tarski @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t63_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ sk_A @ k1_xboole_0 ) )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k2_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X38 @ X39 ) )
      = X38 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('26',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_A
      = ( k1_mcart_1 @ sk_A ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('28',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_A
    = ( k4_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_A
      = ( k4_tarski @ sk_A @ sk_C_1 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X20 ) )
      = ( k1_tarski @ ( k4_tarski @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('38',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ sk_A @ k1_xboole_0 ) )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ X2 )
        = X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('41',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('43',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('45',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t50_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf('46',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X25 @ X26 ) @ X27 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t50_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
   <= ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    sk_A
 != ( k1_mcart_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['43','48'])).

thf('50',plain,
    ( ( sk_A
      = ( k2_mcart_1 @ sk_A ) )
    | ( sk_A
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('51',plain,
    ( sk_A
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['23','51'])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ X2 )
        = X2 )
      | ~ ( r2_hidden @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('54',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qaknUTwstB
% 0.16/0.37  % Computer   : n024.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 17:55:51 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 194 iterations in 0.086s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.40/0.58  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.58  thf(t20_mcart_1, conjecture,
% 0.40/0.58    (![A:$i]:
% 0.40/0.58     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.40/0.58       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i]:
% 0.40/0.58        ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.40/0.58          ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t20_mcart_1])).
% 0.40/0.58  thf('0', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C_1))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(t7_mcart_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.40/0.58       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      (![X38 : $i, X40 : $i]: ((k2_mcart_1 @ (k4_tarski @ X38 @ X40)) = (X40))),
% 0.40/0.58      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.40/0.58  thf('2', plain, (((k2_mcart_1 @ sk_A) = (sk_C_1))),
% 0.40/0.58      inference('sup+', [status(thm)], ['0', '1'])).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      ((((sk_A) = (k1_mcart_1 @ sk_A)) | ((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('4', plain,
% 0.40/0.58      ((((sk_A) = (k2_mcart_1 @ sk_A))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('split', [status(esa)], ['3'])).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      ((((sk_A) = (sk_C_1))) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['2', '4'])).
% 0.40/0.58  thf('6', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C_1))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      ((((sk_A) = (k4_tarski @ sk_B @ sk_A)))
% 0.40/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['5', '6'])).
% 0.40/0.58  thf(t35_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.40/0.58       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      (![X19 : $i, X20 : $i]:
% 0.40/0.58         ((k2_zfmisc_1 @ (k1_tarski @ X19) @ (k1_tarski @ X20))
% 0.40/0.58           = (k1_tarski @ (k4_tarski @ X19 @ X20)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.40/0.58  thf(t135_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.40/0.58         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.40/0.58       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      (![X17 : $i, X18 : $i]:
% 0.40/0.58         (((X17) = (k1_xboole_0))
% 0.40/0.58          | ~ (r1_tarski @ X17 @ (k2_zfmisc_1 @ X18 @ X17)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.40/0.58          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.40/0.58         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.40/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['7', '10'])).
% 0.40/0.58  thf(t69_enumset1, axiom,
% 0.40/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.58  thf('12', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.58  thf(t42_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.40/0.58       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.40/0.58            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.40/0.58  thf('13', plain,
% 0.40/0.58      (![X21 : $i, X23 : $i, X24 : $i]:
% 0.40/0.58         ((r1_tarski @ X23 @ (k2_tarski @ X21 @ X24))
% 0.40/0.58          | ((X23) != (k1_tarski @ X21)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t42_zfmisc_1])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X21 : $i, X24 : $i]:
% 0.40/0.58         (r1_tarski @ (k1_tarski @ X21) @ (k2_tarski @ X21 @ X24))),
% 0.40/0.58      inference('simplify', [status(thm)], ['13'])).
% 0.40/0.58  thf('15', plain,
% 0.40/0.58      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['12', '14'])).
% 0.40/0.58  thf('16', plain,
% 0.40/0.58      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.40/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['11', '15'])).
% 0.40/0.58  thf('17', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.58  thf(t2_boole, axiom,
% 0.40/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.40/0.58  thf(t63_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.40/0.58       ( r2_hidden @ A @ C ) ))).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.40/0.58         ((r2_hidden @ X28 @ X29)
% 0.40/0.58          | ((k3_xboole_0 @ (k2_tarski @ X28 @ X30) @ X29)
% 0.40/0.58              != (k2_tarski @ X28 @ X30)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t63_zfmisc_1])).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (((k1_xboole_0) != (k2_tarski @ X1 @ X0))
% 0.40/0.58          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.58  thf('21', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k1_xboole_0) != (k1_tarski @ X0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['17', '20'])).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      (((((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ sk_A @ k1_xboole_0)))
% 0.40/0.58         <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['16', '21'])).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k2_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.40/0.58  thf('24', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C_1))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('25', plain,
% 0.40/0.58      (![X38 : $i, X39 : $i]: ((k1_mcart_1 @ (k4_tarski @ X38 @ X39)) = (X38))),
% 0.40/0.58      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.40/0.58  thf('26', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.40/0.58      inference('sup+', [status(thm)], ['24', '25'])).
% 0.40/0.58  thf('27', plain,
% 0.40/0.58      ((((sk_A) = (k1_mcart_1 @ sk_A))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('split', [status(esa)], ['3'])).
% 0.40/0.58  thf('28', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['26', '27'])).
% 0.40/0.58  thf('29', plain, (((sk_A) = (k4_tarski @ sk_B @ sk_C_1))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('30', plain,
% 0.40/0.58      ((((sk_A) = (k4_tarski @ sk_A @ sk_C_1)))
% 0.40/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup+', [status(thm)], ['28', '29'])).
% 0.40/0.58  thf('31', plain,
% 0.40/0.58      (![X19 : $i, X20 : $i]:
% 0.40/0.58         ((k2_zfmisc_1 @ (k1_tarski @ X19) @ (k1_tarski @ X20))
% 0.40/0.58           = (k1_tarski @ (k4_tarski @ X19 @ X20)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      (![X17 : $i, X18 : $i]:
% 0.40/0.58         (((X17) = (k1_xboole_0))
% 0.40/0.58          | ~ (r1_tarski @ X17 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         (~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.40/0.58          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      (((~ (r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.40/0.58         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.40/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['30', '33'])).
% 0.40/0.58  thf('35', plain,
% 0.40/0.58      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.40/0.58      inference('sup+', [status(thm)], ['12', '14'])).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.40/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k1_xboole_0) != (k1_tarski @ X0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['17', '20'])).
% 0.40/0.58  thf('38', plain,
% 0.40/0.58      (((((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ sk_A @ k1_xboole_0)))
% 0.40/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.40/0.58  thf('39', plain,
% 0.40/0.58      (((r2_hidden @ sk_A @ k1_xboole_0)) <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('simplify', [status(thm)], ['38'])).
% 0.40/0.58  thf(l22_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( r2_hidden @ A @ B ) =>
% 0.40/0.58       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      (![X2 : $i, X3 : $i]:
% 0.40/0.58         (((k2_xboole_0 @ (k1_tarski @ X3) @ X2) = (X2))
% 0.40/0.58          | ~ (r2_hidden @ X3 @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.40/0.58  thf('41', plain,
% 0.40/0.58      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_xboole_0)))
% 0.40/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.40/0.58  thf('42', plain,
% 0.40/0.58      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.40/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      ((((k2_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))
% 0.40/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['41', '42'])).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.40/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.40/0.58  thf('45', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.58  thf(t50_zfmisc_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.40/0.58  thf('46', plain,
% 0.40/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ (k2_tarski @ X25 @ X26) @ X27) != (k1_xboole_0))),
% 0.40/0.58      inference('cnf', [status(esa)], [t50_zfmisc_1])).
% 0.40/0.58  thf('47', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.40/0.58  thf('48', plain,
% 0.40/0.58      ((![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0)))
% 0.40/0.58         <= ((((sk_A) = (k1_mcart_1 @ sk_A))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['44', '47'])).
% 0.40/0.58  thf('49', plain, (~ (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.40/0.58      inference('simplify_reflect-', [status(thm)], ['43', '48'])).
% 0.40/0.58  thf('50', plain,
% 0.40/0.58      ((((sk_A) = (k2_mcart_1 @ sk_A))) | (((sk_A) = (k1_mcart_1 @ sk_A)))),
% 0.40/0.58      inference('split', [status(esa)], ['3'])).
% 0.40/0.58  thf('51', plain, ((((sk_A) = (k2_mcart_1 @ sk_A)))),
% 0.40/0.58      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 0.40/0.58  thf('52', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.40/0.58      inference('simpl_trail', [status(thm)], ['23', '51'])).
% 0.40/0.58  thf('53', plain,
% 0.40/0.58      (![X2 : $i, X3 : $i]:
% 0.40/0.58         (((k2_xboole_0 @ (k1_tarski @ X3) @ X2) = (X2))
% 0.40/0.58          | ~ (r2_hidden @ X3 @ X2))),
% 0.40/0.58      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.40/0.58  thf('54', plain,
% 0.40/0.58      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.40/0.58  thf('55', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((k2_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_xboole_0))),
% 0.40/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.40/0.58  thf('56', plain, ($false),
% 0.40/0.58      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.40/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
