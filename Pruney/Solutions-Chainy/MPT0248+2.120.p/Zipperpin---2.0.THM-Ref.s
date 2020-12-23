%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4kHVuDWjSr

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 412 expanded)
%              Number of leaves         :   18 ( 107 expanded)
%              Depth                    :   26
%              Number of atoms          :  593 (5706 expanded)
%              Number of equality atoms :  112 (1286 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_C_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('8',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r1_tarski @ X31 @ ( k1_tarski @ X32 ) )
      | ( X31
       != ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('9',plain,(
    ! [X32: $i] :
      ( r1_tarski @ ( k1_tarski @ X32 ) @ ( k1_tarski @ X32 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('14',plain,(
    r1_tarski @ sk_B_1 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31
        = ( k1_tarski @ X30 ) )
      | ( X31 = k1_xboole_0 )
      | ~ ( r1_tarski @ X31 @ ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( sk_B_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','6','29'])).

thf('31',plain,(
    sk_C_1
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['3','30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('32',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('36',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('41',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( X16 = X13 )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('42',plain,(
    ! [X13: $i,X16: $i] :
      ( ( X16 = X13 )
      | ~ ( r2_hidden @ X16 @ ( k1_tarski @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('46',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_C_1
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['3','30'])).

thf('50',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['22'])).

thf('53',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['51','52'])).

thf('54',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['45','53'])).

thf('55',plain,
    ( ( sk_B @ sk_C_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['44','54'])).

thf('56',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('57',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['45','53'])).

thf('59',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('60',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X29 ) @ X28 )
        = X28 )
      | ~ ( r2_hidden @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('61',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k2_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','63'])).

thf('65',plain,(
    sk_C_1
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['3','30'])).

thf('66',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B_1 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['34','66'])).

thf('68',plain,(
    sk_C_1 != sk_C_1 ),
    inference(demod,[status(thm)],['31','67'])).

thf('69',plain,(
    $false ),
    inference(simplify,[status(thm)],['68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4kHVuDWjSr
% 0.14/0.33  % Computer   : n002.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 17:03:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 273 iterations in 0.092s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(t43_zfmisc_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.53          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.53          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.53          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.20/0.53             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.53             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.20/0.53             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.20/0.53         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      ((((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.20/0.53         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 0.20/0.53       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf('7', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(l3_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X31 : $i, X32 : $i]:
% 0.20/0.53         ((r1_tarski @ X31 @ (k1_tarski @ X32)) | ((X31) != (k1_tarski @ X32)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X32 : $i]: (r1_tarski @ (k1_tarski @ X32) @ (k1_tarski @ X32))),
% 0.20/0.53      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ (k1_tarski @ sk_A))),
% 0.20/0.53      inference('sup+', [status(thm)], ['7', '9'])).
% 0.20/0.53  thf('11', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ 
% 0.20/0.53        (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf(t11_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.53         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.20/0.53  thf('14', plain, ((r1_tarski @ sk_B_1 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X30 : $i, X31 : $i]:
% 0.20/0.53         (((X31) = (k1_tarski @ X30))
% 0.20/0.53          | ((X31) = (k1_xboole_0))
% 0.20/0.53          | ~ (r1_tarski @ X31 @ (k1_tarski @ X30)))),
% 0.20/0.53      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.20/0.53          | ((X0) = (k1_xboole_0))
% 0.20/0.53          | ((X0) = (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.20/0.53          | ((X0) = (k1_xboole_0))
% 0.20/0.53          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.20/0.53        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '19'])).
% 0.20/0.53  thf('21', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.20/0.53         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((((sk_B_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.20/0.53         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.20/0.53         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((((sk_B_1) != (sk_B_1)))
% 0.20/0.53         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.20/0.53             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.53  thf('30', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['4', '6', '29'])).
% 0.20/0.53  thf('31', plain, (((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['3', '30'])).
% 0.20/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.53  thf('32', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.53  thf(t12_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]:
% 0.20/0.53         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.53  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.20/0.53        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '19'])).
% 0.20/0.53  thf(t7_xboole_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.53  thf(d3_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.20/0.53       ( ![D:$i]:
% 0.20/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.53           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.53          | (r2_hidden @ X0 @ X2)
% 0.20/0.53          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.20/0.53         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.53      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((X0) = (k1_xboole_0))
% 0.20/0.53          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['36', '38'])).
% 0.20/0.53  thf('40', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d1_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X16 @ X15)
% 0.20/0.53          | ((X16) = (X13))
% 0.20/0.53          | ((X15) != (k1_tarski @ X13)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X13 : $i, X16 : $i]:
% 0.20/0.53         (((X16) = (X13)) | ~ (r2_hidden @ X16 @ (k1_tarski @ X13)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.20/0.53          | ((X0) = (sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '42'])).
% 0.20/0.53  thf('44', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B @ sk_C_1) = (sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['39', '43'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['22'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.53  thf('47', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      ((![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 0.20/0.53         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.53  thf('49', plain, (((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['3', '30'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      ((((sk_C_1) != (sk_C_1))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.53  thf('51', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['22'])).
% 0.20/0.53  thf('53', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['51', '52'])).
% 0.20/0.53  thf('54', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['45', '53'])).
% 0.20/0.53  thf('55', plain, (((sk_B @ sk_C_1) = (sk_A))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['44', '54'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ sk_C_1) | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['55', '56'])).
% 0.20/0.53  thf('58', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['45', '53'])).
% 0.20/0.53  thf('59', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf(l22_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.53       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X28 : $i, X29 : $i]:
% 0.20/0.53         (((k2_xboole_0 @ (k1_tarski @ X29) @ X28) = (X28))
% 0.20/0.53          | ~ (r2_hidden @ X29 @ X28))),
% 0.20/0.53      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.20/0.53  thf('61', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1) = (sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.53  thf('62', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (((k2_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_C_1) = (sk_C_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['61', '62'])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      ((((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))
% 0.20/0.53        | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['35', '63'])).
% 0.20/0.53  thf('65', plain, (((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['3', '30'])).
% 0.20/0.53  thf('66', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.20/0.53  thf('67', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['34', '66'])).
% 0.20/0.53  thf('68', plain, (((sk_C_1) != (sk_C_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['31', '67'])).
% 0.20/0.53  thf('69', plain, ($false), inference('simplify', [status(thm)], ['68'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
