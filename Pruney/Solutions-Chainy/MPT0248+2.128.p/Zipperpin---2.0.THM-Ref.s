%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vfbRLf2gMT

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:36 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 268 expanded)
%              Number of leaves         :   19 (  75 expanded)
%              Depth                    :   19
%              Number of atoms          :  591 (3568 expanded)
%              Number of equality atoms :  104 ( 794 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_C_2
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X62: $i,X63: $i] :
      ( ( X63
        = ( k1_tarski @ X62 ) )
      | ( X63 = k1_xboole_0 )
      | ~ ( r1_tarski @ X63 @ ( k1_tarski @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[t39_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','6','22'])).

thf('24',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('26',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('27',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X52 ) @ X53 )
      | ~ ( r2_hidden @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('33',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X54 ) @ X55 )
      | ( r2_hidden @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('34',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X11 @ X14 )
      | ~ ( r1_xboole_0 @ X11 @ ( k2_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_C_2 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X52 ) @ X53 )
      | ~ ( r2_hidden @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_C_2 @ sk_B )
    | ( r1_tarski @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( sk_C_2
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('54',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('57',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['55','56'])).

thf('58',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['49','57'])).

thf('59',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('60',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['48','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['31','60'])).

thf('62',plain,(
    sk_C_2 != sk_C_2 ),
    inference(demod,[status(thm)],['24','61'])).

thf('63',plain,(
    $false ),
    inference(simplify,[status(thm)],['62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vfbRLf2gMT
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.93  % Solved by: fo/fo7.sh
% 0.75/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.93  % done 938 iterations in 0.476s
% 0.75/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.93  % SZS output start Refutation
% 0.75/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.93  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.93  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.75/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.93  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.75/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.93  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.93  thf(t43_zfmisc_1, conjecture,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.75/0.93          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.75/0.93          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.75/0.93          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.75/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.93    (~( ![A:$i,B:$i,C:$i]:
% 0.75/0.93        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.75/0.93             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.75/0.93             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.75/0.93             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.75/0.93    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.75/0.93  thf('0', plain,
% 0.75/0.93      ((((sk_B) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('1', plain,
% 0.75/0.93      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.75/0.93         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.75/0.93      inference('split', [status(esa)], ['0'])).
% 0.75/0.93  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('3', plain,
% 0.75/0.93      ((((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.75/0.93         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.75/0.93      inference('demod', [status(thm)], ['1', '2'])).
% 0.75/0.93  thf('4', plain,
% 0.75/0.93      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.75/0.93      inference('split', [status(esa)], ['0'])).
% 0.75/0.93  thf('5', plain,
% 0.75/0.93      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('6', plain,
% 0.75/0.93      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.75/0.93      inference('split', [status(esa)], ['5'])).
% 0.75/0.93  thf(t7_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.93  thf('7', plain,
% 0.75/0.93      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.75/0.93      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.75/0.93  thf('8', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(t39_zfmisc_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.75/0.93       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.75/0.93  thf('9', plain,
% 0.75/0.93      (![X62 : $i, X63 : $i]:
% 0.75/0.93         (((X63) = (k1_tarski @ X62))
% 0.75/0.93          | ((X63) = (k1_xboole_0))
% 0.75/0.93          | ~ (r1_tarski @ X63 @ (k1_tarski @ X62)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t39_zfmisc_1])).
% 0.75/0.93  thf('10', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.75/0.93          | ((X0) = (k1_xboole_0))
% 0.75/0.93          | ((X0) = (k1_tarski @ sk_A)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['8', '9'])).
% 0.75/0.93  thf('11', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('12', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.75/0.93          | ((X0) = (k1_xboole_0))
% 0.75/0.93          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.75/0.93      inference('demod', [status(thm)], ['10', '11'])).
% 0.75/0.93  thf('13', plain,
% 0.75/0.93      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['7', '12'])).
% 0.75/0.93  thf('14', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('15', plain,
% 0.75/0.93      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('16', plain,
% 0.75/0.93      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.75/0.93      inference('split', [status(esa)], ['15'])).
% 0.75/0.93  thf('17', plain,
% 0.75/0.93      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.75/0.93         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['14', '16'])).
% 0.75/0.93  thf('18', plain,
% 0.75/0.93      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.75/0.93         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['13', '17'])).
% 0.75/0.93  thf('19', plain,
% 0.75/0.93      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.75/0.93      inference('simplify', [status(thm)], ['18'])).
% 0.75/0.93  thf('20', plain,
% 0.75/0.93      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.75/0.93      inference('split', [status(esa)], ['0'])).
% 0.75/0.93  thf('21', plain,
% 0.75/0.93      ((((sk_B) != (sk_B)))
% 0.75/0.93         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['19', '20'])).
% 0.75/0.93  thf('22', plain,
% 0.75/0.93      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.75/0.93      inference('simplify', [status(thm)], ['21'])).
% 0.75/0.93  thf('23', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.75/0.93      inference('sat_resolution*', [status(thm)], ['4', '6', '22'])).
% 0.75/0.93  thf('24', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.75/0.93      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.75/0.93  thf(d3_tarski, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( r1_tarski @ A @ B ) <=>
% 0.75/0.93       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.75/0.93  thf('25', plain,
% 0.75/0.93      (![X1 : $i, X3 : $i]:
% 0.75/0.93         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.93  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.75/0.93  thf('26', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.75/0.93      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.75/0.93  thf(l24_zfmisc_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.75/0.93  thf('27', plain,
% 0.75/0.93      (![X52 : $i, X53 : $i]:
% 0.75/0.93         (~ (r1_xboole_0 @ (k1_tarski @ X52) @ X53) | ~ (r2_hidden @ X52 @ X53))),
% 0.75/0.93      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.75/0.93  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.75/0.93      inference('sup-', [status(thm)], ['26', '27'])).
% 0.75/0.93  thf('29', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.75/0.93      inference('sup-', [status(thm)], ['25', '28'])).
% 0.75/0.93  thf(t12_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.75/0.93  thf('30', plain,
% 0.75/0.93      (![X6 : $i, X7 : $i]:
% 0.75/0.93         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.75/0.93      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.75/0.93  thf('31', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['29', '30'])).
% 0.75/0.93  thf('32', plain,
% 0.75/0.93      (![X1 : $i, X3 : $i]:
% 0.75/0.93         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.93  thf(l27_zfmisc_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.75/0.93  thf('33', plain,
% 0.75/0.93      (![X54 : $i, X55 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ (k1_tarski @ X54) @ X55) | (r2_hidden @ X54 @ X55))),
% 0.75/0.93      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.75/0.93  thf('34', plain,
% 0.75/0.93      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['7', '12'])).
% 0.75/0.93  thf(t70_xboole_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.75/0.93            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.75/0.93       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.75/0.93            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.75/0.93  thf('35', plain,
% 0.75/0.93      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.75/0.93         ((r1_xboole_0 @ X11 @ X14)
% 0.75/0.93          | ~ (r1_xboole_0 @ X11 @ (k2_xboole_0 @ X12 @ X14)))),
% 0.75/0.93      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.75/0.93  thf('36', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (r1_xboole_0 @ X0 @ sk_B)
% 0.75/0.93          | ((sk_B) = (k1_xboole_0))
% 0.75/0.93          | (r1_xboole_0 @ X0 @ sk_C_2))),
% 0.75/0.93      inference('sup-', [status(thm)], ['34', '35'])).
% 0.75/0.93  thf('37', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((r2_hidden @ X0 @ sk_B)
% 0.75/0.93          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_C_2)
% 0.75/0.93          | ((sk_B) = (k1_xboole_0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['33', '36'])).
% 0.75/0.93  thf('38', plain,
% 0.75/0.93      (![X52 : $i, X53 : $i]:
% 0.75/0.93         (~ (r1_xboole_0 @ (k1_tarski @ X52) @ X53) | ~ (r2_hidden @ X52 @ X53))),
% 0.75/0.93      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.75/0.93  thf('39', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (((sk_B) = (k1_xboole_0))
% 0.75/0.93          | (r2_hidden @ X0 @ sk_B)
% 0.75/0.93          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.75/0.93      inference('sup-', [status(thm)], ['37', '38'])).
% 0.75/0.93  thf('40', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((r1_tarski @ sk_C_2 @ X0)
% 0.75/0.93          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B)
% 0.75/0.93          | ((sk_B) = (k1_xboole_0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['32', '39'])).
% 0.75/0.93  thf('41', plain,
% 0.75/0.93      (![X1 : $i, X3 : $i]:
% 0.75/0.93         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.75/0.93      inference('cnf', [status(esa)], [d3_tarski])).
% 0.75/0.93  thf('42', plain,
% 0.75/0.93      ((((sk_B) = (k1_xboole_0))
% 0.75/0.93        | (r1_tarski @ sk_C_2 @ sk_B)
% 0.75/0.93        | (r1_tarski @ sk_C_2 @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['40', '41'])).
% 0.75/0.93  thf('43', plain, (((r1_tarski @ sk_C_2 @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.75/0.93      inference('simplify', [status(thm)], ['42'])).
% 0.75/0.93  thf('44', plain,
% 0.75/0.93      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['7', '12'])).
% 0.75/0.93  thf('45', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.75/0.93          | ((X0) = (k1_xboole_0))
% 0.75/0.93          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 0.75/0.93      inference('demod', [status(thm)], ['10', '11'])).
% 0.75/0.93  thf('46', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (~ (r1_tarski @ X0 @ sk_B)
% 0.75/0.93          | ((sk_B) = (k1_xboole_0))
% 0.75/0.93          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.75/0.93          | ((X0) = (k1_xboole_0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['44', '45'])).
% 0.75/0.93  thf('47', plain,
% 0.75/0.93      ((((sk_B) = (k1_xboole_0))
% 0.75/0.93        | ((sk_C_2) = (k1_xboole_0))
% 0.75/0.93        | ((sk_C_2) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.75/0.93        | ((sk_B) = (k1_xboole_0)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['43', '46'])).
% 0.75/0.93  thf('48', plain,
% 0.75/0.93      ((((sk_C_2) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 0.75/0.93        | ((sk_C_2) = (k1_xboole_0))
% 0.75/0.93        | ((sk_B) = (k1_xboole_0)))),
% 0.75/0.93      inference('simplify', [status(thm)], ['47'])).
% 0.75/0.93  thf('49', plain,
% 0.75/0.93      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.75/0.93      inference('split', [status(esa)], ['15'])).
% 0.75/0.93  thf('50', plain,
% 0.75/0.93      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.75/0.93      inference('simplify', [status(thm)], ['18'])).
% 0.75/0.93  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['29', '30'])).
% 0.75/0.93  thf('52', plain,
% 0.75/0.93      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.75/0.93         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.75/0.93      inference('sup+', [status(thm)], ['50', '51'])).
% 0.75/0.93  thf('53', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.75/0.93      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.75/0.93  thf('54', plain,
% 0.75/0.93      ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['52', '53'])).
% 0.75/0.93  thf('55', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.75/0.93      inference('simplify', [status(thm)], ['54'])).
% 0.75/0.93  thf('56', plain,
% 0.75/0.93      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.75/0.93      inference('split', [status(esa)], ['15'])).
% 0.75/0.93  thf('57', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.75/0.93      inference('sat_resolution*', [status(thm)], ['55', '56'])).
% 0.75/0.93  thf('58', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.75/0.93      inference('simpl_trail', [status(thm)], ['49', '57'])).
% 0.75/0.93  thf('59', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.75/0.93      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 0.75/0.93  thf('60', plain, (((sk_B) = (k1_xboole_0))),
% 0.75/0.93      inference('simplify_reflect-', [status(thm)], ['48', '58', '59'])).
% 0.75/0.93  thf('61', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 0.75/0.93      inference('demod', [status(thm)], ['31', '60'])).
% 0.75/0.93  thf('62', plain, (((sk_C_2) != (sk_C_2))),
% 0.75/0.93      inference('demod', [status(thm)], ['24', '61'])).
% 0.75/0.93  thf('63', plain, ($false), inference('simplify', [status(thm)], ['62'])).
% 0.75/0.93  
% 0.75/0.93  % SZS output end Refutation
% 0.75/0.93  
% 0.75/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
