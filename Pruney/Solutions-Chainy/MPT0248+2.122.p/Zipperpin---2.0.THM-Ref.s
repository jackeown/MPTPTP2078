%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nsKAYhxqnq

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:36 EST 2020

% Result     : Theorem 6.85s
% Output     : Refutation 6.85s
% Verified   : 
% Statistics : Number of formulae       :  209 (2696 expanded)
%              Number of leaves         :   13 ( 648 expanded)
%              Depth                    :   34
%              Number of atoms          : 2236 (36429 expanded)
%              Number of equality atoms :  382 (6505 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X11: $i] :
      ( ( X11
        = ( k1_tarski @ X7 ) )
      | ( ( sk_C @ X11 @ X7 )
        = X7 )
      | ( r2_hidden @ ( sk_C @ X11 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = X1 )
      | ( X0
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ ( k1_tarski @ sk_A ) )
      | ( sk_C_1
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_C_1 @ X0 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('7',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_C_1 @ X0 )
        = X0 )
      | ( sk_C_1
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_C_1 @ X0 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X7: $i,X11: $i] :
      ( ( X11
        = ( k1_tarski @ X7 ) )
      | ( ( sk_C @ X11 @ X7 )
        = X7 )
      | ( r2_hidden @ ( sk_C @ X11 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_C_1 )
      | ( sk_C_1
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_C_1 @ X0 )
        = X0 )
      | ( ( sk_C @ sk_C_1 @ X0 )
        = X0 )
      | ( sk_C_1
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_C_1 @ X0 )
        = X0 )
      | ( sk_C_1
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ sk_A @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_C_1 @ X0 )
        = X0 )
      | ( sk_C_1
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_C_1 @ X0 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C @ sk_C_1 @ X0 )
        = sk_A )
      | ( sk_C_1
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,
    ( ( sk_C_1
      = ( k1_tarski @ sk_A ) )
    | ( ( sk_C @ sk_C_1 @ sk_A )
      = sk_A ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X7: $i,X11: $i] :
      ( ( X11
        = ( k1_tarski @ X7 ) )
      | ( ( sk_C @ X11 @ X7 )
       != X7 )
      | ~ ( r2_hidden @ ( sk_C @ X11 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('16',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) )
    | ( ( sk_C @ sk_C_1 @ sk_A )
     != sk_A )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( sk_C @ sk_C_1 @ sk_A )
     != sk_A )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( sk_C_1
      = ( k1_tarski @ sk_A ) )
    | ( ( sk_C @ sk_C_1 @ sk_A )
      = sk_A ) ),
    inference(simplify,[status(thm)],['13'])).

thf('19',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_C_1 @ X0 )
        = X0 )
      | ( sk_C_1
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('25',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_C_1 @ X0 )
        = X0 )
      | ( sk_C_1
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('29',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1 != sk_C_1 )
        | ( ( sk_C @ sk_C_1 @ X0 )
          = X0 )
        | ( sk_C_1
          = ( k1_tarski @ X0 ) ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1
          = ( k1_tarski @ X0 ) )
        | ( ( sk_C @ sk_C_1 @ X0 )
          = X0 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X7: $i,X11: $i] :
      ( ( X11
        = ( k1_tarski @ X7 ) )
      | ( ( sk_C @ X11 @ X7 )
       != X7 )
      | ~ ( r2_hidden @ ( sk_C @ X11 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ( sk_C_1
          = ( k1_tarski @ X0 ) )
        | ( ( sk_C @ sk_C_1 @ X0 )
         != X0 )
        | ( sk_C_1
          = ( k1_tarski @ X0 ) ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( ( sk_C @ sk_C_1 @ X0 )
         != X0 )
        | ( sk_C_1
          = ( k1_tarski @ X0 ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_C_1
        = ( k1_tarski @ sk_A ) )
      | ( ( sk_C @ sk_C_1 @ sk_A )
       != sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['29'])).

thf('38',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( ( sk_C @ sk_C_1 @ sk_A )
       != sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_C_1
        = ( k1_tarski @ sk_A ) )
      | ( sk_C_1
        = ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','38'])).

thf('40',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_C_1
        = ( k1_tarski @ sk_A ) ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['29'])).

thf('42',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X7: $i,X11: $i] :
      ( ( X11
        = ( k1_tarski @ X7 ) )
      | ( ( sk_C @ X11 @ X7 )
        = X7 )
      | ( r2_hidden @ ( sk_C @ X11 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = X1 )
      | ( X0
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_B @ X0 ) @ ( k1_tarski @ sk_A ) )
      | ( sk_B
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_B @ X0 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['43','47'])).

thf('49',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_B @ X0 )
        = X0 )
      | ( sk_B
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_B @ X0 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C @ sk_B @ X0 )
        = sk_A )
      | ( sk_B
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['50'])).

thf('52',plain,
    ( ( sk_B
      = ( k1_tarski @ sk_A ) )
    | ( ( sk_C @ sk_B @ sk_A )
      = sk_A ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X7: $i,X11: $i] :
      ( ( X11
        = ( k1_tarski @ X7 ) )
      | ( ( sk_C @ X11 @ X7 )
       != X7 )
      | ~ ( r2_hidden @ ( sk_C @ X11 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('54',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_tarski @ sk_A ) )
    | ( ( sk_C @ sk_B @ sk_A )
     != sk_A )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
     != sk_A )
    | ( sk_B
      = ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( sk_B
      = ( k1_tarski @ sk_A ) )
    | ( ( sk_C @ sk_B @ sk_A )
      = sk_A ) ),
    inference(simplify,[status(thm)],['51'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B
      = ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','57'])).

thf('59',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_C_1
       != ( k1_tarski @ sk_A ) )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,
    ( ( sk_B
      = ( k1_tarski @ sk_A ) )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['29'])).

thf('64',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_B @ X0 )
        = X0 )
      | ( sk_B
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_B @ X0 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('67',plain,(
    ! [X7: $i,X11: $i] :
      ( ( X11
        = ( k1_tarski @ X7 ) )
      | ( ( sk_C @ X11 @ X7 )
        = X7 )
      | ( r2_hidden @ ( sk_C @ X11 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_B
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_B @ X0 )
        = X0 )
      | ( ( sk_C @ sk_B @ X0 )
        = X0 )
      | ( sk_B
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_B @ X0 )
        = X0 )
      | ( sk_B
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_B @ X0 )
        = X0 )
      | ( sk_B
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('73',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('74',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ sk_B @ X0 )
        = X0 )
      | ( sk_B
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('76',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['59'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( sk_B != sk_B )
        | ( ( sk_C @ sk_B @ X0 )
          = X0 )
        | ( sk_B
          = ( k1_tarski @ X0 ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k1_tarski @ X0 ) )
        | ( ( sk_C @ sk_B @ X0 )
          = X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X7: $i,X11: $i] :
      ( ( X11
        = ( k1_tarski @ X7 ) )
      | ( ( sk_C @ X11 @ X7 )
       != X7 )
      | ~ ( r2_hidden @ ( sk_C @ X11 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( sk_B
          = ( k1_tarski @ X0 ) )
        | ( ( sk_C @ sk_B @ X0 )
         != X0 )
        | ( sk_B
          = ( k1_tarski @ X0 ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ( ( sk_C @ sk_B @ X0 )
         != X0 )
        | ( sk_B
          = ( k1_tarski @ X0 ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( ( sk_C_1
        = ( k1_tarski @ sk_A ) )
      | ( sk_B
        = ( k1_tarski @ sk_A ) )
      | ( ( sk_C @ sk_B @ sk_A )
       != sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['59'])).

thf('84',plain,
    ( ( ( sk_C_1
        = ( k1_tarski @ sk_A ) )
      | ( ( sk_C @ sk_B @ sk_A )
       != sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_B
        = ( k1_tarski @ sk_A ) )
      | ( sk_B
        = ( k1_tarski @ sk_A ) )
      | ( sk_C_1
        = ( k1_tarski @ sk_A ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','84'])).

thf('86',plain,
    ( ( ( sk_C_1
        = ( k1_tarski @ sk_A ) )
      | ( sk_B
        = ( k1_tarski @ sk_A ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['59'])).

thf('88',plain,
    ( ( sk_C_1
      = ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( sk_C_1
      = ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('90',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('92',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('93',plain,
    ( ( sk_C_1
      = ( k1_tarski @ sk_A ) )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_C_1
      = ( k1_tarski @ sk_A ) )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('95',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['98'])).

thf('100',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['98'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('108',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['106','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['97','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
        = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) ) ) )
      | ( sk_B
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['94','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
        = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ X0 @ sk_C_1 ) ) )
      | ( sk_B
        = ( k1_tarski @ sk_A ) )
      | ( sk_B
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['93','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_tarski @ sk_A ) )
      | ( ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
        = ( k2_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ X0 @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k2_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['90','116'])).

thf('118',plain,
    ( ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
        = ( k2_xboole_0 @ sk_C_1 @ sk_C_1 ) )
      | ( sk_B
        = ( k1_tarski @ sk_A ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['89','117'])).

thf('119',plain,
    ( ( sk_C_1
      = ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('120',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['121'])).

thf('123',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['121'])).

thf('127',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( sk_C_1
      = ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('129',plain,
    ( ( ( ( k2_xboole_0 @ sk_B @ sk_C_1 )
        = sk_C_1 )
      | ( sk_B = sk_C_1 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['118','119','127','128'])).

thf('130',plain,
    ( ( sk_C_1
      = ( k1_tarski @ sk_A ) )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('131',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['59'])).

thf('132',plain,
    ( ( ( sk_B != sk_C_1 )
      | ( sk_B
        = ( k1_tarski @ sk_A ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['59'])).

thf('134',plain,
    ( ( sk_B != sk_C_1 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( k2_xboole_0 @ sk_B @ sk_C_1 )
      = sk_C_1 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['129','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ sk_B ) @ sk_C_1 )
        | ( X0
          = ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['135','138'])).

thf('140',plain,
    ( ( sk_C_1
      = ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('141',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('142',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C_1 )
        | ( X0 = sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ! [X0: $i] :
        ( ( X0
          = ( k2_xboole_0 @ sk_B @ X0 ) )
        | ( ( sk_D @ X0 @ X0 @ sk_B )
          = sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('145',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ sk_B )
        | ( X0
          = ( k2_xboole_0 @ sk_B @ X0 ) )
        | ( X0
          = ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,
    ( ! [X0: $i] :
        ( ( X0
          = ( k2_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('148',plain,
    ( ! [X0: $i] :
        ( ( X0
          = ( k2_xboole_0 @ sk_B @ X0 ) )
        | ( sk_B
          = ( k1_tarski @ sk_A ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('149',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('150',plain,
    ( ( ( k1_xboole_0 = sk_B )
      | ( sk_B
        = ( k1_tarski @ sk_A ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( ( sk_B = sk_C_1 )
      | ( k1_xboole_0 = sk_B ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['88','150'])).

thf('152',plain,
    ( ( sk_B != sk_C_1 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['132','133'])).

thf('153',plain,
    ( ( k1_xboole_0 = sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('155',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( sk_B
      = ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','57'])).

thf('158',plain,
    ( ( sk_B
      = ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','57'])).

thf('159',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('161',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['159','165'])).

thf('167',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['158','168'])).

thf('170',plain,
    ( ( sk_B
      = ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','57'])).

thf('171',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('173',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ sk_C_1 ) @ sk_B )
        | ( X0
          = ( k2_xboole_0 @ sk_C_1 @ X0 ) ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( sk_B
      = ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','57'])).

thf('175',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('176',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( X0 = sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ! [X0: $i] :
        ( ( X0
          = ( k2_xboole_0 @ sk_C_1 @ X0 ) )
        | ( ( sk_D @ X0 @ X0 @ sk_C_1 )
          = sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('179',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ sk_C_1 )
        | ( X0
          = ( k2_xboole_0 @ sk_C_1 @ X0 ) )
        | ( X0
          = ( k2_xboole_0 @ sk_C_1 @ X0 ) ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,
    ( ! [X0: $i] :
        ( ( X0
          = ( k2_xboole_0 @ sk_C_1 @ X0 ) )
        | ( r2_hidden @ sk_A @ sk_C_1 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('182',plain,
    ( ! [X0: $i] :
        ( ( X0
          = ( k2_xboole_0 @ sk_C_1 @ X0 ) )
        | ( sk_C_1
          = ( k1_tarski @ sk_A ) ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('184',plain,
    ( ( ( k1_xboole_0 = sk_C_1 )
      | ( sk_C_1
        = ( k1_tarski @ sk_A ) ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( ( sk_C_1 = sk_B )
      | ( k1_xboole_0 = sk_C_1 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['157','184'])).

thf('186',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['29'])).

thf('187',plain,
    ( ( sk_B
      = ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','57'])).

thf('188',plain,
    ( ( sk_C_1 != sk_B )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( k1_xboole_0 = sk_C_1 )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['185','188'])).

thf('190',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['59'])).

thf('191',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_C_1
       != ( k1_tarski @ sk_A ) )
      & ( sk_C_1 != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['191'])).

thf('193',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['59'])).

thf('194',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['62','63','65','156','192','193'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nsKAYhxqnq
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.85/7.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.85/7.07  % Solved by: fo/fo7.sh
% 6.85/7.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.85/7.07  % done 4190 iterations in 6.612s
% 6.85/7.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.85/7.07  % SZS output start Refutation
% 6.85/7.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.85/7.07  thf(sk_B_type, type, sk_B: $i).
% 6.85/7.07  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.85/7.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.85/7.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.85/7.07  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 6.85/7.07  thf(sk_A_type, type, sk_A: $i).
% 6.85/7.07  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.85/7.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.85/7.07  thf(t43_zfmisc_1, conjecture,
% 6.85/7.07    (![A:$i,B:$i,C:$i]:
% 6.85/7.07     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 6.85/7.07          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 6.85/7.07          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 6.85/7.07          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 6.85/7.07  thf(zf_stmt_0, negated_conjecture,
% 6.85/7.07    (~( ![A:$i,B:$i,C:$i]:
% 6.85/7.07        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 6.85/7.07             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 6.85/7.07             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 6.85/7.07             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 6.85/7.07    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 6.85/7.07  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 6.85/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.85/7.07  thf(d1_tarski, axiom,
% 6.85/7.07    (![A:$i,B:$i]:
% 6.85/7.07     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 6.85/7.07       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 6.85/7.07  thf('1', plain,
% 6.85/7.07      (![X7 : $i, X11 : $i]:
% 6.85/7.07         (((X11) = (k1_tarski @ X7))
% 6.85/7.07          | ((sk_C @ X11 @ X7) = (X7))
% 6.85/7.07          | (r2_hidden @ (sk_C @ X11 @ X7) @ X11))),
% 6.85/7.07      inference('cnf', [status(esa)], [d1_tarski])).
% 6.85/7.07  thf(d3_xboole_0, axiom,
% 6.85/7.07    (![A:$i,B:$i,C:$i]:
% 6.85/7.07     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 6.85/7.07       ( ![D:$i]:
% 6.85/7.07         ( ( r2_hidden @ D @ C ) <=>
% 6.85/7.07           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 6.85/7.07  thf('2', plain,
% 6.85/7.07      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.85/7.07         (~ (r2_hidden @ X0 @ X1)
% 6.85/7.07          | (r2_hidden @ X0 @ X2)
% 6.85/7.07          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 6.85/7.07      inference('cnf', [status(esa)], [d3_xboole_0])).
% 6.85/7.07  thf('3', plain,
% 6.85/7.07      (![X0 : $i, X1 : $i, X3 : $i]:
% 6.85/7.07         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 6.85/7.07      inference('simplify', [status(thm)], ['2'])).
% 6.85/7.07  thf('4', plain,
% 6.85/7.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.07         (((sk_C @ X0 @ X1) = (X1))
% 6.85/7.07          | ((X0) = (k1_tarski @ X1))
% 6.85/7.07          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0)))),
% 6.85/7.07      inference('sup-', [status(thm)], ['1', '3'])).
% 6.85/7.07  thf('5', plain,
% 6.85/7.07      (![X0 : $i]:
% 6.85/7.07         ((r2_hidden @ (sk_C @ sk_C_1 @ X0) @ (k1_tarski @ sk_A))
% 6.85/7.07          | ((sk_C_1) = (k1_tarski @ X0))
% 6.85/7.07          | ((sk_C @ sk_C_1 @ X0) = (X0)))),
% 6.85/7.07      inference('sup+', [status(thm)], ['0', '4'])).
% 6.85/7.07  thf('6', plain,
% 6.85/7.07      (![X7 : $i, X9 : $i, X10 : $i]:
% 6.85/7.07         (~ (r2_hidden @ X10 @ X9)
% 6.85/7.07          | ((X10) = (X7))
% 6.85/7.07          | ((X9) != (k1_tarski @ X7)))),
% 6.85/7.07      inference('cnf', [status(esa)], [d1_tarski])).
% 6.85/7.07  thf('7', plain,
% 6.85/7.07      (![X7 : $i, X10 : $i]:
% 6.85/7.07         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 6.85/7.07      inference('simplify', [status(thm)], ['6'])).
% 6.85/7.07  thf('8', plain,
% 6.85/7.07      (![X0 : $i]:
% 6.85/7.07         (((sk_C @ sk_C_1 @ X0) = (X0))
% 6.85/7.07          | ((sk_C_1) = (k1_tarski @ X0))
% 6.85/7.07          | ((sk_C @ sk_C_1 @ X0) = (sk_A)))),
% 6.85/7.07      inference('sup-', [status(thm)], ['5', '7'])).
% 6.85/7.07  thf('9', plain,
% 6.85/7.07      (![X7 : $i, X11 : $i]:
% 6.85/7.07         (((X11) = (k1_tarski @ X7))
% 6.85/7.07          | ((sk_C @ X11 @ X7) = (X7))
% 6.85/7.07          | (r2_hidden @ (sk_C @ X11 @ X7) @ X11))),
% 6.85/7.07      inference('cnf', [status(esa)], [d1_tarski])).
% 6.85/7.07  thf('10', plain,
% 6.85/7.07      (![X0 : $i]:
% 6.85/7.07         ((r2_hidden @ sk_A @ sk_C_1)
% 6.85/7.07          | ((sk_C_1) = (k1_tarski @ X0))
% 6.85/7.07          | ((sk_C @ sk_C_1 @ X0) = (X0))
% 6.85/7.07          | ((sk_C @ sk_C_1 @ X0) = (X0))
% 6.85/7.07          | ((sk_C_1) = (k1_tarski @ X0)))),
% 6.85/7.07      inference('sup+', [status(thm)], ['8', '9'])).
% 6.85/7.07  thf('11', plain,
% 6.85/7.07      (![X0 : $i]:
% 6.85/7.07         (((sk_C @ sk_C_1 @ X0) = (X0))
% 6.85/7.07          | ((sk_C_1) = (k1_tarski @ X0))
% 6.85/7.07          | (r2_hidden @ sk_A @ sk_C_1))),
% 6.85/7.07      inference('simplify', [status(thm)], ['10'])).
% 6.85/7.07  thf('12', plain,
% 6.85/7.07      (![X0 : $i]:
% 6.85/7.07         (((sk_C @ sk_C_1 @ X0) = (X0))
% 6.85/7.07          | ((sk_C_1) = (k1_tarski @ X0))
% 6.85/7.07          | ((sk_C @ sk_C_1 @ X0) = (sk_A)))),
% 6.85/7.07      inference('sup-', [status(thm)], ['5', '7'])).
% 6.85/7.07  thf('13', plain,
% 6.85/7.07      (![X0 : $i]:
% 6.85/7.07         (((X0) != (sk_A))
% 6.85/7.07          | ((sk_C @ sk_C_1 @ X0) = (sk_A))
% 6.85/7.07          | ((sk_C_1) = (k1_tarski @ X0)))),
% 6.85/7.07      inference('eq_fact', [status(thm)], ['12'])).
% 6.85/7.07  thf('14', plain,
% 6.85/7.07      ((((sk_C_1) = (k1_tarski @ sk_A)) | ((sk_C @ sk_C_1 @ sk_A) = (sk_A)))),
% 6.85/7.07      inference('simplify', [status(thm)], ['13'])).
% 6.85/7.07  thf('15', plain,
% 6.85/7.07      (![X7 : $i, X11 : $i]:
% 6.85/7.07         (((X11) = (k1_tarski @ X7))
% 6.85/7.07          | ((sk_C @ X11 @ X7) != (X7))
% 6.85/7.07          | ~ (r2_hidden @ (sk_C @ X11 @ X7) @ X11))),
% 6.85/7.07      inference('cnf', [status(esa)], [d1_tarski])).
% 6.85/7.07  thf('16', plain,
% 6.85/7.07      ((~ (r2_hidden @ sk_A @ sk_C_1)
% 6.85/7.07        | ((sk_C_1) = (k1_tarski @ sk_A))
% 6.85/7.07        | ((sk_C @ sk_C_1 @ sk_A) != (sk_A))
% 6.85/7.07        | ((sk_C_1) = (k1_tarski @ sk_A)))),
% 6.85/7.07      inference('sup-', [status(thm)], ['14', '15'])).
% 6.85/7.07  thf('17', plain,
% 6.85/7.07      ((((sk_C @ sk_C_1 @ sk_A) != (sk_A))
% 6.85/7.07        | ((sk_C_1) = (k1_tarski @ sk_A))
% 6.85/7.07        | ~ (r2_hidden @ sk_A @ sk_C_1))),
% 6.85/7.07      inference('simplify', [status(thm)], ['16'])).
% 6.85/7.07  thf('18', plain,
% 6.85/7.07      ((((sk_C_1) = (k1_tarski @ sk_A)) | ((sk_C @ sk_C_1 @ sk_A) = (sk_A)))),
% 6.85/7.07      inference('simplify', [status(thm)], ['13'])).
% 6.85/7.07  thf('19', plain,
% 6.85/7.07      ((~ (r2_hidden @ sk_A @ sk_C_1) | ((sk_C_1) = (k1_tarski @ sk_A)))),
% 6.85/7.07      inference('clc', [status(thm)], ['17', '18'])).
% 6.85/7.07  thf('20', plain,
% 6.85/7.07      (![X0 : $i]:
% 6.85/7.07         (((sk_C_1) = (k1_tarski @ X0))
% 6.85/7.07          | ((sk_C @ sk_C_1 @ X0) = (X0))
% 6.85/7.07          | ((sk_C_1) = (k1_tarski @ sk_A)))),
% 6.85/7.07      inference('sup-', [status(thm)], ['11', '19'])).
% 6.85/7.07  thf('21', plain,
% 6.85/7.07      (![X7 : $i, X8 : $i, X9 : $i]:
% 6.85/7.07         (((X8) != (X7)) | (r2_hidden @ X8 @ X9) | ((X9) != (k1_tarski @ X7)))),
% 6.85/7.07      inference('cnf', [status(esa)], [d1_tarski])).
% 6.85/7.07  thf('22', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 6.85/7.07      inference('simplify', [status(thm)], ['21'])).
% 6.85/7.07  thf('23', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 6.85/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.85/7.07  thf('24', plain,
% 6.85/7.07      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 6.85/7.07         (~ (r2_hidden @ X4 @ X2)
% 6.85/7.07          | (r2_hidden @ X4 @ X3)
% 6.85/7.07          | (r2_hidden @ X4 @ X1)
% 6.85/7.07          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 6.85/7.07      inference('cnf', [status(esa)], [d3_xboole_0])).
% 6.85/7.07  thf('25', plain,
% 6.85/7.07      (![X1 : $i, X3 : $i, X4 : $i]:
% 6.85/7.07         ((r2_hidden @ X4 @ X1)
% 6.85/7.07          | (r2_hidden @ X4 @ X3)
% 6.85/7.07          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 6.85/7.07      inference('simplify', [status(thm)], ['24'])).
% 6.85/7.07  thf('26', plain,
% 6.85/7.07      (![X0 : $i]:
% 6.85/7.07         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 6.85/7.07          | (r2_hidden @ X0 @ sk_B)
% 6.85/7.07          | (r2_hidden @ X0 @ sk_C_1))),
% 6.85/7.07      inference('sup-', [status(thm)], ['23', '25'])).
% 6.85/7.07  thf('27', plain, (((r2_hidden @ sk_A @ sk_C_1) | (r2_hidden @ sk_A @ sk_B))),
% 6.85/7.07      inference('sup-', [status(thm)], ['22', '26'])).
% 6.85/7.07  thf('28', plain,
% 6.85/7.07      (![X0 : $i]:
% 6.85/7.07         (((sk_C_1) = (k1_tarski @ X0))
% 6.85/7.07          | ((sk_C @ sk_C_1 @ X0) = (X0))
% 6.85/7.07          | ((sk_C_1) = (k1_tarski @ sk_A)))),
% 6.85/7.07      inference('sup-', [status(thm)], ['11', '19'])).
% 6.85/7.07  thf('29', plain,
% 6.85/7.07      ((((sk_B) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 6.85/7.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.85/7.07  thf('30', plain,
% 6.85/7.07      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 6.85/7.07         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.07      inference('split', [status(esa)], ['29'])).
% 6.85/7.07  thf('31', plain,
% 6.85/7.07      ((![X0 : $i]:
% 6.85/7.07          (((sk_C_1) != (sk_C_1))
% 6.85/7.07           | ((sk_C @ sk_C_1 @ X0) = (X0))
% 6.85/7.07           | ((sk_C_1) = (k1_tarski @ X0))))
% 6.85/7.07         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.07      inference('sup-', [status(thm)], ['28', '30'])).
% 6.85/7.07  thf('32', plain,
% 6.85/7.07      ((![X0 : $i]:
% 6.85/7.07          (((sk_C_1) = (k1_tarski @ X0)) | ((sk_C @ sk_C_1 @ X0) = (X0))))
% 6.85/7.07         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.07      inference('simplify', [status(thm)], ['31'])).
% 6.85/7.08  thf('33', plain,
% 6.85/7.08      (![X7 : $i, X11 : $i]:
% 6.85/7.08         (((X11) = (k1_tarski @ X7))
% 6.85/7.08          | ((sk_C @ X11 @ X7) != (X7))
% 6.85/7.08          | ~ (r2_hidden @ (sk_C @ X11 @ X7) @ X11))),
% 6.85/7.08      inference('cnf', [status(esa)], [d1_tarski])).
% 6.85/7.08  thf('34', plain,
% 6.85/7.08      ((![X0 : $i]:
% 6.85/7.08          (~ (r2_hidden @ X0 @ sk_C_1)
% 6.85/7.08           | ((sk_C_1) = (k1_tarski @ X0))
% 6.85/7.08           | ((sk_C @ sk_C_1 @ X0) != (X0))
% 6.85/7.08           | ((sk_C_1) = (k1_tarski @ X0))))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['32', '33'])).
% 6.85/7.08  thf('35', plain,
% 6.85/7.08      ((![X0 : $i]:
% 6.85/7.08          (((sk_C @ sk_C_1 @ X0) != (X0))
% 6.85/7.08           | ((sk_C_1) = (k1_tarski @ X0))
% 6.85/7.08           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify', [status(thm)], ['34'])).
% 6.85/7.08  thf('36', plain,
% 6.85/7.08      ((((r2_hidden @ sk_A @ sk_B)
% 6.85/7.08         | ((sk_C_1) = (k1_tarski @ sk_A))
% 6.85/7.08         | ((sk_C @ sk_C_1 @ sk_A) != (sk_A))))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['27', '35'])).
% 6.85/7.08  thf('37', plain,
% 6.85/7.08      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('split', [status(esa)], ['29'])).
% 6.85/7.08  thf('38', plain,
% 6.85/7.08      ((((r2_hidden @ sk_A @ sk_B) | ((sk_C @ sk_C_1 @ sk_A) != (sk_A))))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 6.85/7.08  thf('39', plain,
% 6.85/7.08      (((((sk_A) != (sk_A))
% 6.85/7.08         | ((sk_C_1) = (k1_tarski @ sk_A))
% 6.85/7.08         | ((sk_C_1) = (k1_tarski @ sk_A))
% 6.85/7.08         | (r2_hidden @ sk_A @ sk_B))) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['20', '38'])).
% 6.85/7.08  thf('40', plain,
% 6.85/7.08      ((((r2_hidden @ sk_A @ sk_B) | ((sk_C_1) = (k1_tarski @ sk_A))))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify', [status(thm)], ['39'])).
% 6.85/7.08  thf('41', plain,
% 6.85/7.08      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('split', [status(esa)], ['29'])).
% 6.85/7.08  thf('42', plain,
% 6.85/7.08      (((r2_hidden @ sk_A @ sk_B)) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 6.85/7.08  thf('43', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 6.85/7.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.85/7.08  thf('44', plain,
% 6.85/7.08      (![X7 : $i, X11 : $i]:
% 6.85/7.08         (((X11) = (k1_tarski @ X7))
% 6.85/7.08          | ((sk_C @ X11 @ X7) = (X7))
% 6.85/7.08          | (r2_hidden @ (sk_C @ X11 @ X7) @ X11))),
% 6.85/7.08      inference('cnf', [status(esa)], [d1_tarski])).
% 6.85/7.08  thf('45', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.85/7.08         (~ (r2_hidden @ X0 @ X3)
% 6.85/7.08          | (r2_hidden @ X0 @ X2)
% 6.85/7.08          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 6.85/7.08      inference('cnf', [status(esa)], [d3_xboole_0])).
% 6.85/7.08  thf('46', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i, X3 : $i]:
% 6.85/7.08         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 6.85/7.08      inference('simplify', [status(thm)], ['45'])).
% 6.85/7.08  thf('47', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.08         (((sk_C @ X0 @ X1) = (X1))
% 6.85/7.08          | ((X0) = (k1_tarski @ X1))
% 6.85/7.08          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['44', '46'])).
% 6.85/7.08  thf('48', plain,
% 6.85/7.08      (![X0 : $i]:
% 6.85/7.08         ((r2_hidden @ (sk_C @ sk_B @ X0) @ (k1_tarski @ sk_A))
% 6.85/7.08          | ((sk_B) = (k1_tarski @ X0))
% 6.85/7.08          | ((sk_C @ sk_B @ X0) = (X0)))),
% 6.85/7.08      inference('sup+', [status(thm)], ['43', '47'])).
% 6.85/7.08  thf('49', plain,
% 6.85/7.08      (![X7 : $i, X10 : $i]:
% 6.85/7.08         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 6.85/7.08      inference('simplify', [status(thm)], ['6'])).
% 6.85/7.08  thf('50', plain,
% 6.85/7.08      (![X0 : $i]:
% 6.85/7.08         (((sk_C @ sk_B @ X0) = (X0))
% 6.85/7.08          | ((sk_B) = (k1_tarski @ X0))
% 6.85/7.08          | ((sk_C @ sk_B @ X0) = (sk_A)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['48', '49'])).
% 6.85/7.08  thf('51', plain,
% 6.85/7.08      (![X0 : $i]:
% 6.85/7.08         (((X0) != (sk_A))
% 6.85/7.08          | ((sk_C @ sk_B @ X0) = (sk_A))
% 6.85/7.08          | ((sk_B) = (k1_tarski @ X0)))),
% 6.85/7.08      inference('eq_fact', [status(thm)], ['50'])).
% 6.85/7.08  thf('52', plain,
% 6.85/7.08      ((((sk_B) = (k1_tarski @ sk_A)) | ((sk_C @ sk_B @ sk_A) = (sk_A)))),
% 6.85/7.08      inference('simplify', [status(thm)], ['51'])).
% 6.85/7.08  thf('53', plain,
% 6.85/7.08      (![X7 : $i, X11 : $i]:
% 6.85/7.08         (((X11) = (k1_tarski @ X7))
% 6.85/7.08          | ((sk_C @ X11 @ X7) != (X7))
% 6.85/7.08          | ~ (r2_hidden @ (sk_C @ X11 @ X7) @ X11))),
% 6.85/7.08      inference('cnf', [status(esa)], [d1_tarski])).
% 6.85/7.08  thf('54', plain,
% 6.85/7.08      ((~ (r2_hidden @ sk_A @ sk_B)
% 6.85/7.08        | ((sk_B) = (k1_tarski @ sk_A))
% 6.85/7.08        | ((sk_C @ sk_B @ sk_A) != (sk_A))
% 6.85/7.08        | ((sk_B) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['52', '53'])).
% 6.85/7.08  thf('55', plain,
% 6.85/7.08      ((((sk_C @ sk_B @ sk_A) != (sk_A))
% 6.85/7.08        | ((sk_B) = (k1_tarski @ sk_A))
% 6.85/7.08        | ~ (r2_hidden @ sk_A @ sk_B))),
% 6.85/7.08      inference('simplify', [status(thm)], ['54'])).
% 6.85/7.08  thf('56', plain,
% 6.85/7.08      ((((sk_B) = (k1_tarski @ sk_A)) | ((sk_C @ sk_B @ sk_A) = (sk_A)))),
% 6.85/7.08      inference('simplify', [status(thm)], ['51'])).
% 6.85/7.08  thf('57', plain,
% 6.85/7.08      ((~ (r2_hidden @ sk_A @ sk_B) | ((sk_B) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('clc', [status(thm)], ['55', '56'])).
% 6.85/7.08  thf('58', plain,
% 6.85/7.08      ((((sk_B) = (k1_tarski @ sk_A))) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['42', '57'])).
% 6.85/7.08  thf('59', plain,
% 6.85/7.08      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 6.85/7.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.85/7.08  thf('60', plain,
% 6.85/7.08      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('split', [status(esa)], ['59'])).
% 6.85/7.08  thf('61', plain,
% 6.85/7.08      ((((sk_B) != (sk_B)))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))) & 
% 6.85/7.08             ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['58', '60'])).
% 6.85/7.08  thf('62', plain,
% 6.85/7.08      ((((sk_B) = (k1_tarski @ sk_A))) | (((sk_C_1) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('simplify', [status(thm)], ['61'])).
% 6.85/7.08  thf('63', plain,
% 6.85/7.08      (~ (((sk_B) = (k1_xboole_0))) | ~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('split', [status(esa)], ['29'])).
% 6.85/7.08  thf('64', plain,
% 6.85/7.08      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.85/7.08  thf('65', plain,
% 6.85/7.08      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('split', [status(esa)], ['64'])).
% 6.85/7.08  thf('66', plain,
% 6.85/7.08      (![X0 : $i]:
% 6.85/7.08         (((sk_C @ sk_B @ X0) = (X0))
% 6.85/7.08          | ((sk_B) = (k1_tarski @ X0))
% 6.85/7.08          | ((sk_C @ sk_B @ X0) = (sk_A)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['48', '49'])).
% 6.85/7.08  thf('67', plain,
% 6.85/7.08      (![X7 : $i, X11 : $i]:
% 6.85/7.08         (((X11) = (k1_tarski @ X7))
% 6.85/7.08          | ((sk_C @ X11 @ X7) = (X7))
% 6.85/7.08          | (r2_hidden @ (sk_C @ X11 @ X7) @ X11))),
% 6.85/7.08      inference('cnf', [status(esa)], [d1_tarski])).
% 6.85/7.08  thf('68', plain,
% 6.85/7.08      (![X0 : $i]:
% 6.85/7.08         ((r2_hidden @ sk_A @ sk_B)
% 6.85/7.08          | ((sk_B) = (k1_tarski @ X0))
% 6.85/7.08          | ((sk_C @ sk_B @ X0) = (X0))
% 6.85/7.08          | ((sk_C @ sk_B @ X0) = (X0))
% 6.85/7.08          | ((sk_B) = (k1_tarski @ X0)))),
% 6.85/7.08      inference('sup+', [status(thm)], ['66', '67'])).
% 6.85/7.08  thf('69', plain,
% 6.85/7.08      (![X0 : $i]:
% 6.85/7.08         (((sk_C @ sk_B @ X0) = (X0))
% 6.85/7.08          | ((sk_B) = (k1_tarski @ X0))
% 6.85/7.08          | (r2_hidden @ sk_A @ sk_B))),
% 6.85/7.08      inference('simplify', [status(thm)], ['68'])).
% 6.85/7.08  thf('70', plain,
% 6.85/7.08      ((~ (r2_hidden @ sk_A @ sk_B) | ((sk_B) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('clc', [status(thm)], ['55', '56'])).
% 6.85/7.08  thf('71', plain,
% 6.85/7.08      (![X0 : $i]:
% 6.85/7.08         (((sk_B) = (k1_tarski @ X0))
% 6.85/7.08          | ((sk_C @ sk_B @ X0) = (X0))
% 6.85/7.08          | ((sk_B) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['69', '70'])).
% 6.85/7.08  thf('72', plain, (((r2_hidden @ sk_A @ sk_C_1) | (r2_hidden @ sk_A @ sk_B))),
% 6.85/7.08      inference('sup-', [status(thm)], ['22', '26'])).
% 6.85/7.08  thf('73', plain,
% 6.85/7.08      ((~ (r2_hidden @ sk_A @ sk_C_1) | ((sk_C_1) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('clc', [status(thm)], ['17', '18'])).
% 6.85/7.08  thf('74', plain,
% 6.85/7.08      (((r2_hidden @ sk_A @ sk_B) | ((sk_C_1) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['72', '73'])).
% 6.85/7.08  thf('75', plain,
% 6.85/7.08      (![X0 : $i]:
% 6.85/7.08         (((sk_B) = (k1_tarski @ X0))
% 6.85/7.08          | ((sk_C @ sk_B @ X0) = (X0))
% 6.85/7.08          | ((sk_B) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['69', '70'])).
% 6.85/7.08  thf('76', plain,
% 6.85/7.08      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('split', [status(esa)], ['59'])).
% 6.85/7.08  thf('77', plain,
% 6.85/7.08      ((![X0 : $i]:
% 6.85/7.08          (((sk_B) != (sk_B))
% 6.85/7.08           | ((sk_C @ sk_B @ X0) = (X0))
% 6.85/7.08           | ((sk_B) = (k1_tarski @ X0))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['75', '76'])).
% 6.85/7.08  thf('78', plain,
% 6.85/7.08      ((![X0 : $i]: (((sk_B) = (k1_tarski @ X0)) | ((sk_C @ sk_B @ X0) = (X0))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify', [status(thm)], ['77'])).
% 6.85/7.08  thf('79', plain,
% 6.85/7.08      (![X7 : $i, X11 : $i]:
% 6.85/7.08         (((X11) = (k1_tarski @ X7))
% 6.85/7.08          | ((sk_C @ X11 @ X7) != (X7))
% 6.85/7.08          | ~ (r2_hidden @ (sk_C @ X11 @ X7) @ X11))),
% 6.85/7.08      inference('cnf', [status(esa)], [d1_tarski])).
% 6.85/7.08  thf('80', plain,
% 6.85/7.08      ((![X0 : $i]:
% 6.85/7.08          (~ (r2_hidden @ X0 @ sk_B)
% 6.85/7.08           | ((sk_B) = (k1_tarski @ X0))
% 6.85/7.08           | ((sk_C @ sk_B @ X0) != (X0))
% 6.85/7.08           | ((sk_B) = (k1_tarski @ X0))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['78', '79'])).
% 6.85/7.08  thf('81', plain,
% 6.85/7.08      ((![X0 : $i]:
% 6.85/7.08          (((sk_C @ sk_B @ X0) != (X0))
% 6.85/7.08           | ((sk_B) = (k1_tarski @ X0))
% 6.85/7.08           | ~ (r2_hidden @ X0 @ sk_B)))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify', [status(thm)], ['80'])).
% 6.85/7.08  thf('82', plain,
% 6.85/7.08      (((((sk_C_1) = (k1_tarski @ sk_A))
% 6.85/7.08         | ((sk_B) = (k1_tarski @ sk_A))
% 6.85/7.08         | ((sk_C @ sk_B @ sk_A) != (sk_A))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['74', '81'])).
% 6.85/7.08  thf('83', plain,
% 6.85/7.08      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('split', [status(esa)], ['59'])).
% 6.85/7.08  thf('84', plain,
% 6.85/7.08      (((((sk_C_1) = (k1_tarski @ sk_A)) | ((sk_C @ sk_B @ sk_A) != (sk_A))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 6.85/7.08  thf('85', plain,
% 6.85/7.08      (((((sk_A) != (sk_A))
% 6.85/7.08         | ((sk_B) = (k1_tarski @ sk_A))
% 6.85/7.08         | ((sk_B) = (k1_tarski @ sk_A))
% 6.85/7.08         | ((sk_C_1) = (k1_tarski @ sk_A))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['71', '84'])).
% 6.85/7.08  thf('86', plain,
% 6.85/7.08      (((((sk_C_1) = (k1_tarski @ sk_A)) | ((sk_B) = (k1_tarski @ sk_A))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify', [status(thm)], ['85'])).
% 6.85/7.08  thf('87', plain,
% 6.85/7.08      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('split', [status(esa)], ['59'])).
% 6.85/7.08  thf('88', plain,
% 6.85/7.08      ((((sk_C_1) = (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 6.85/7.08  thf('89', plain,
% 6.85/7.08      ((((sk_C_1) = (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 6.85/7.08  thf('90', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 6.85/7.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.85/7.08  thf('91', plain,
% 6.85/7.08      (((r2_hidden @ sk_A @ sk_B) | ((sk_C_1) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['72', '73'])).
% 6.85/7.08  thf('92', plain,
% 6.85/7.08      ((~ (r2_hidden @ sk_A @ sk_B) | ((sk_B) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('clc', [status(thm)], ['55', '56'])).
% 6.85/7.08  thf('93', plain,
% 6.85/7.08      ((((sk_C_1) = (k1_tarski @ sk_A)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['91', '92'])).
% 6.85/7.08  thf('94', plain,
% 6.85/7.08      ((((sk_C_1) = (k1_tarski @ sk_A)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['91', '92'])).
% 6.85/7.08  thf('95', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 6.85/7.08      inference('simplify', [status(thm)], ['21'])).
% 6.85/7.08  thf('96', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i, X3 : $i]:
% 6.85/7.08         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 6.85/7.08      inference('simplify', [status(thm)], ['2'])).
% 6.85/7.08  thf('97', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['95', '96'])).
% 6.85/7.08  thf('98', plain,
% 6.85/7.08      (![X1 : $i, X3 : $i, X5 : $i]:
% 6.85/7.08         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 6.85/7.08          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 6.85/7.08          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 6.85/7.08          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 6.85/7.08      inference('cnf', [status(esa)], [d3_xboole_0])).
% 6.85/7.08  thf('99', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 6.85/7.08          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 6.85/7.08          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 6.85/7.08      inference('eq_fact', [status(thm)], ['98'])).
% 6.85/7.08  thf('100', plain,
% 6.85/7.08      (![X1 : $i, X3 : $i, X5 : $i]:
% 6.85/7.08         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 6.85/7.08          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 6.85/7.08          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 6.85/7.08      inference('cnf', [status(esa)], [d3_xboole_0])).
% 6.85/7.08  thf('101', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 6.85/7.08          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 6.85/7.08          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 6.85/7.08          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['99', '100'])).
% 6.85/7.08  thf('102', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 6.85/7.08          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 6.85/7.08          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 6.85/7.08      inference('simplify', [status(thm)], ['101'])).
% 6.85/7.08  thf('103', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 6.85/7.08          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 6.85/7.08          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 6.85/7.08      inference('eq_fact', [status(thm)], ['98'])).
% 6.85/7.08  thf('104', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 6.85/7.08          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 6.85/7.08      inference('clc', [status(thm)], ['102', '103'])).
% 6.85/7.08  thf('105', plain,
% 6.85/7.08      (![X7 : $i, X10 : $i]:
% 6.85/7.08         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 6.85/7.08      inference('simplify', [status(thm)], ['6'])).
% 6.85/7.08  thf('106', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         (((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 6.85/7.08          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['104', '105'])).
% 6.85/7.08  thf('107', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 6.85/7.08          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 6.85/7.08      inference('clc', [status(thm)], ['102', '103'])).
% 6.85/7.08  thf('108', plain,
% 6.85/7.08      (![X1 : $i, X3 : $i, X5 : $i]:
% 6.85/7.08         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 6.85/7.08          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 6.85/7.08          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 6.85/7.08      inference('cnf', [status(esa)], [d3_xboole_0])).
% 6.85/7.08  thf('109', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 6.85/7.08          | ~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 6.85/7.08          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['107', '108'])).
% 6.85/7.08  thf('110', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         (~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 6.85/7.08          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 6.85/7.08      inference('simplify', [status(thm)], ['109'])).
% 6.85/7.08  thf('111', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         (~ (r2_hidden @ X0 @ X1)
% 6.85/7.08          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 6.85/7.08          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['106', '110'])).
% 6.85/7.08  thf('112', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         (((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 6.85/7.08          | ~ (r2_hidden @ X0 @ X1))),
% 6.85/7.08      inference('simplify', [status(thm)], ['111'])).
% 6.85/7.08  thf('113', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0))
% 6.85/7.08           = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 6.85/7.08              (k2_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['97', '112'])).
% 6.85/7.08  thf('114', plain,
% 6.85/7.08      (![X0 : $i]:
% 6.85/7.08         (((k2_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 6.85/7.08            = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ X0 @ (k1_tarski @ sk_A))))
% 6.85/7.08          | ((sk_B) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('sup+', [status(thm)], ['94', '113'])).
% 6.85/7.08  thf('115', plain,
% 6.85/7.08      (![X0 : $i]:
% 6.85/7.08         (((k2_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 6.85/7.08            = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ X0 @ sk_C_1)))
% 6.85/7.08          | ((sk_B) = (k1_tarski @ sk_A))
% 6.85/7.08          | ((sk_B) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('sup+', [status(thm)], ['93', '114'])).
% 6.85/7.08  thf('116', plain,
% 6.85/7.08      (![X0 : $i]:
% 6.85/7.08         (((sk_B) = (k1_tarski @ sk_A))
% 6.85/7.08          | ((k2_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 6.85/7.08              = (k2_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ X0 @ sk_C_1))))),
% 6.85/7.08      inference('simplify', [status(thm)], ['115'])).
% 6.85/7.08  thf('117', plain,
% 6.85/7.08      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 6.85/7.08          = (k2_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)))
% 6.85/7.08        | ((sk_B) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('sup+', [status(thm)], ['90', '116'])).
% 6.85/7.08  thf('118', plain,
% 6.85/7.08      (((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 6.85/7.08           = (k2_xboole_0 @ sk_C_1 @ sk_C_1))
% 6.85/7.08         | ((sk_B) = (k1_tarski @ sk_A))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup+', [status(thm)], ['89', '117'])).
% 6.85/7.08  thf('119', plain,
% 6.85/7.08      ((((sk_C_1) = (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 6.85/7.08  thf('120', plain,
% 6.85/7.08      (![X1 : $i, X3 : $i, X5 : $i]:
% 6.85/7.08         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 6.85/7.08          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 6.85/7.08          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 6.85/7.08          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 6.85/7.08      inference('cnf', [status(esa)], [d3_xboole_0])).
% 6.85/7.08  thf('121', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 6.85/7.08          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X0)
% 6.85/7.08          | ((X1) = (k2_xboole_0 @ X0 @ X0)))),
% 6.85/7.08      inference('eq_fact', [status(thm)], ['120'])).
% 6.85/7.08  thf('122', plain,
% 6.85/7.08      (![X0 : $i]:
% 6.85/7.08         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 6.85/7.08          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 6.85/7.08      inference('eq_fact', [status(thm)], ['121'])).
% 6.85/7.08  thf('123', plain,
% 6.85/7.08      (![X1 : $i, X3 : $i, X5 : $i]:
% 6.85/7.08         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 6.85/7.08          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 6.85/7.08          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 6.85/7.08      inference('cnf', [status(esa)], [d3_xboole_0])).
% 6.85/7.08  thf('124', plain,
% 6.85/7.08      (![X0 : $i]:
% 6.85/7.08         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 6.85/7.08          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 6.85/7.08          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['122', '123'])).
% 6.85/7.08  thf('125', plain,
% 6.85/7.08      (![X0 : $i]:
% 6.85/7.08         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 6.85/7.08          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 6.85/7.08      inference('simplify', [status(thm)], ['124'])).
% 6.85/7.08  thf('126', plain,
% 6.85/7.08      (![X0 : $i]:
% 6.85/7.08         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 6.85/7.08          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 6.85/7.08      inference('eq_fact', [status(thm)], ['121'])).
% 6.85/7.08  thf('127', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 6.85/7.08      inference('clc', [status(thm)], ['125', '126'])).
% 6.85/7.08  thf('128', plain,
% 6.85/7.08      ((((sk_C_1) = (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 6.85/7.08  thf('129', plain,
% 6.85/7.08      (((((k2_xboole_0 @ sk_B @ sk_C_1) = (sk_C_1)) | ((sk_B) = (sk_C_1))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('demod', [status(thm)], ['118', '119', '127', '128'])).
% 6.85/7.08  thf('130', plain,
% 6.85/7.08      ((((sk_C_1) = (k1_tarski @ sk_A)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['91', '92'])).
% 6.85/7.08  thf('131', plain,
% 6.85/7.08      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('split', [status(esa)], ['59'])).
% 6.85/7.08  thf('132', plain,
% 6.85/7.08      (((((sk_B) != (sk_C_1)) | ((sk_B) = (k1_tarski @ sk_A))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['130', '131'])).
% 6.85/7.08  thf('133', plain,
% 6.85/7.08      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('split', [status(esa)], ['59'])).
% 6.85/7.08  thf('134', plain,
% 6.85/7.08      ((((sk_B) != (sk_C_1))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify_reflect-', [status(thm)], ['132', '133'])).
% 6.85/7.08  thf('135', plain,
% 6.85/7.08      ((((k2_xboole_0 @ sk_B @ sk_C_1) = (sk_C_1)))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify_reflect-', [status(thm)], ['129', '134'])).
% 6.85/7.08  thf('136', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 6.85/7.08          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 6.85/7.08      inference('clc', [status(thm)], ['102', '103'])).
% 6.85/7.08  thf('137', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i, X3 : $i]:
% 6.85/7.08         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 6.85/7.08      inference('simplify', [status(thm)], ['45'])).
% 6.85/7.08  thf('138', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.08         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 6.85/7.08          | (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['136', '137'])).
% 6.85/7.08  thf('139', plain,
% 6.85/7.08      ((![X0 : $i]:
% 6.85/7.08          ((r2_hidden @ (sk_D @ X0 @ X0 @ sk_B) @ sk_C_1)
% 6.85/7.08           | ((X0) = (k2_xboole_0 @ sk_B @ X0))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup+', [status(thm)], ['135', '138'])).
% 6.85/7.08  thf('140', plain,
% 6.85/7.08      ((((sk_C_1) = (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 6.85/7.08  thf('141', plain,
% 6.85/7.08      (![X7 : $i, X10 : $i]:
% 6.85/7.08         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 6.85/7.08      inference('simplify', [status(thm)], ['6'])).
% 6.85/7.08  thf('142', plain,
% 6.85/7.08      ((![X0 : $i]: (~ (r2_hidden @ X0 @ sk_C_1) | ((X0) = (sk_A))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['140', '141'])).
% 6.85/7.08  thf('143', plain,
% 6.85/7.08      ((![X0 : $i]:
% 6.85/7.08          (((X0) = (k2_xboole_0 @ sk_B @ X0))
% 6.85/7.08           | ((sk_D @ X0 @ X0 @ sk_B) = (sk_A))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['139', '142'])).
% 6.85/7.08  thf('144', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 6.85/7.08          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 6.85/7.08      inference('clc', [status(thm)], ['102', '103'])).
% 6.85/7.08  thf('145', plain,
% 6.85/7.08      ((![X0 : $i]:
% 6.85/7.08          ((r2_hidden @ sk_A @ sk_B)
% 6.85/7.08           | ((X0) = (k2_xboole_0 @ sk_B @ X0))
% 6.85/7.08           | ((X0) = (k2_xboole_0 @ sk_B @ X0))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup+', [status(thm)], ['143', '144'])).
% 6.85/7.08  thf('146', plain,
% 6.85/7.08      ((![X0 : $i]:
% 6.85/7.08          (((X0) = (k2_xboole_0 @ sk_B @ X0)) | (r2_hidden @ sk_A @ sk_B)))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify', [status(thm)], ['145'])).
% 6.85/7.08  thf('147', plain,
% 6.85/7.08      ((~ (r2_hidden @ sk_A @ sk_B) | ((sk_B) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('clc', [status(thm)], ['55', '56'])).
% 6.85/7.08  thf('148', plain,
% 6.85/7.08      ((![X0 : $i]:
% 6.85/7.08          (((X0) = (k2_xboole_0 @ sk_B @ X0)) | ((sk_B) = (k1_tarski @ sk_A))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['146', '147'])).
% 6.85/7.08  thf(t1_boole, axiom,
% 6.85/7.08    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 6.85/7.08  thf('149', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 6.85/7.08      inference('cnf', [status(esa)], [t1_boole])).
% 6.85/7.08  thf('150', plain,
% 6.85/7.08      (((((k1_xboole_0) = (sk_B)) | ((sk_B) = (k1_tarski @ sk_A))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup+', [status(thm)], ['148', '149'])).
% 6.85/7.08  thf('151', plain,
% 6.85/7.08      (((((sk_B) = (sk_C_1)) | ((k1_xboole_0) = (sk_B))))
% 6.85/7.08         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup+', [status(thm)], ['88', '150'])).
% 6.85/7.08  thf('152', plain,
% 6.85/7.08      ((((sk_B) != (sk_C_1))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify_reflect-', [status(thm)], ['132', '133'])).
% 6.85/7.08  thf('153', plain,
% 6.85/7.08      ((((k1_xboole_0) = (sk_B))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify_reflect-', [status(thm)], ['151', '152'])).
% 6.85/7.08  thf('154', plain,
% 6.85/7.08      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 6.85/7.08      inference('split', [status(esa)], ['29'])).
% 6.85/7.08  thf('155', plain,
% 6.85/7.08      ((((k1_xboole_0) != (k1_xboole_0)))
% 6.85/7.08         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['153', '154'])).
% 6.85/7.08  thf('156', plain,
% 6.85/7.08      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('simplify', [status(thm)], ['155'])).
% 6.85/7.08  thf('157', plain,
% 6.85/7.08      ((((sk_B) = (k1_tarski @ sk_A))) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['42', '57'])).
% 6.85/7.08  thf('158', plain,
% 6.85/7.08      ((((sk_B) = (k1_tarski @ sk_A))) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['42', '57'])).
% 6.85/7.08  thf('159', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 6.85/7.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.85/7.08  thf('160', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 6.85/7.08          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 6.85/7.08      inference('clc', [status(thm)], ['102', '103'])).
% 6.85/7.08  thf('161', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i, X3 : $i]:
% 6.85/7.08         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 6.85/7.08      inference('simplify', [status(thm)], ['2'])).
% 6.85/7.08  thf('162', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.08         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 6.85/7.08          | (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['160', '161'])).
% 6.85/7.08  thf('163', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         (~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 6.85/7.08          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 6.85/7.08      inference('simplify', [status(thm)], ['109'])).
% 6.85/7.08  thf('164', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         (((k2_xboole_0 @ X1 @ X0)
% 6.85/7.08            = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))
% 6.85/7.08          | ((k2_xboole_0 @ X1 @ X0)
% 6.85/7.08              = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['162', '163'])).
% 6.85/7.08  thf('165', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         ((k2_xboole_0 @ X1 @ X0)
% 6.85/7.08           = (k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 6.85/7.08      inference('simplify', [status(thm)], ['164'])).
% 6.85/7.08  thf('166', plain,
% 6.85/7.08      (((k2_xboole_0 @ sk_B @ sk_C_1)
% 6.85/7.08         = (k2_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('sup+', [status(thm)], ['159', '165'])).
% 6.85/7.08  thf('167', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 6.85/7.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.85/7.08  thf('168', plain,
% 6.85/7.08      (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('demod', [status(thm)], ['166', '167'])).
% 6.85/7.08  thf('169', plain,
% 6.85/7.08      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_C_1 @ sk_B)))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup+', [status(thm)], ['158', '168'])).
% 6.85/7.08  thf('170', plain,
% 6.85/7.08      ((((sk_B) = (k1_tarski @ sk_A))) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['42', '57'])).
% 6.85/7.08  thf('171', plain,
% 6.85/7.08      ((((sk_B) = (k2_xboole_0 @ sk_C_1 @ sk_B)))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('demod', [status(thm)], ['169', '170'])).
% 6.85/7.08  thf('172', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.85/7.08         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 6.85/7.08          | (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 6.85/7.08      inference('sup-', [status(thm)], ['136', '137'])).
% 6.85/7.08  thf('173', plain,
% 6.85/7.08      ((![X0 : $i]:
% 6.85/7.08          ((r2_hidden @ (sk_D @ X0 @ X0 @ sk_C_1) @ sk_B)
% 6.85/7.08           | ((X0) = (k2_xboole_0 @ sk_C_1 @ X0))))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup+', [status(thm)], ['171', '172'])).
% 6.85/7.08  thf('174', plain,
% 6.85/7.08      ((((sk_B) = (k1_tarski @ sk_A))) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['42', '57'])).
% 6.85/7.08  thf('175', plain,
% 6.85/7.08      (![X7 : $i, X10 : $i]:
% 6.85/7.08         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 6.85/7.08      inference('simplify', [status(thm)], ['6'])).
% 6.85/7.08  thf('176', plain,
% 6.85/7.08      ((![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B) | ((X0) = (sk_A))))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['174', '175'])).
% 6.85/7.08  thf('177', plain,
% 6.85/7.08      ((![X0 : $i]:
% 6.85/7.08          (((X0) = (k2_xboole_0 @ sk_C_1 @ X0))
% 6.85/7.08           | ((sk_D @ X0 @ X0 @ sk_C_1) = (sk_A))))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['173', '176'])).
% 6.85/7.08  thf('178', plain,
% 6.85/7.08      (![X0 : $i, X1 : $i]:
% 6.85/7.08         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 6.85/7.08          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 6.85/7.08      inference('clc', [status(thm)], ['102', '103'])).
% 6.85/7.08  thf('179', plain,
% 6.85/7.08      ((![X0 : $i]:
% 6.85/7.08          ((r2_hidden @ sk_A @ sk_C_1)
% 6.85/7.08           | ((X0) = (k2_xboole_0 @ sk_C_1 @ X0))
% 6.85/7.08           | ((X0) = (k2_xboole_0 @ sk_C_1 @ X0))))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup+', [status(thm)], ['177', '178'])).
% 6.85/7.08  thf('180', plain,
% 6.85/7.08      ((![X0 : $i]:
% 6.85/7.08          (((X0) = (k2_xboole_0 @ sk_C_1 @ X0)) | (r2_hidden @ sk_A @ sk_C_1)))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify', [status(thm)], ['179'])).
% 6.85/7.08  thf('181', plain,
% 6.85/7.08      ((~ (r2_hidden @ sk_A @ sk_C_1) | ((sk_C_1) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('clc', [status(thm)], ['17', '18'])).
% 6.85/7.08  thf('182', plain,
% 6.85/7.08      ((![X0 : $i]:
% 6.85/7.08          (((X0) = (k2_xboole_0 @ sk_C_1 @ X0))
% 6.85/7.08           | ((sk_C_1) = (k1_tarski @ sk_A))))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['180', '181'])).
% 6.85/7.08  thf('183', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 6.85/7.08      inference('cnf', [status(esa)], [t1_boole])).
% 6.85/7.08  thf('184', plain,
% 6.85/7.08      (((((k1_xboole_0) = (sk_C_1)) | ((sk_C_1) = (k1_tarski @ sk_A))))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup+', [status(thm)], ['182', '183'])).
% 6.85/7.08  thf('185', plain,
% 6.85/7.08      (((((sk_C_1) = (sk_B)) | ((k1_xboole_0) = (sk_C_1))))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup+', [status(thm)], ['157', '184'])).
% 6.85/7.08  thf('186', plain,
% 6.85/7.08      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('split', [status(esa)], ['29'])).
% 6.85/7.08  thf('187', plain,
% 6.85/7.08      ((((sk_B) = (k1_tarski @ sk_A))) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['42', '57'])).
% 6.85/7.08  thf('188', plain,
% 6.85/7.08      ((((sk_C_1) != (sk_B))) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('demod', [status(thm)], ['186', '187'])).
% 6.85/7.08  thf('189', plain,
% 6.85/7.08      ((((k1_xboole_0) = (sk_C_1))) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 6.85/7.08      inference('simplify_reflect-', [status(thm)], ['185', '188'])).
% 6.85/7.08  thf('190', plain,
% 6.85/7.08      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 6.85/7.08      inference('split', [status(esa)], ['59'])).
% 6.85/7.08  thf('191', plain,
% 6.85/7.08      ((((k1_xboole_0) != (k1_xboole_0)))
% 6.85/7.08         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))) & 
% 6.85/7.08             ~ (((sk_C_1) = (k1_xboole_0))))),
% 6.85/7.08      inference('sup-', [status(thm)], ['189', '190'])).
% 6.85/7.08  thf('192', plain,
% 6.85/7.08      ((((sk_C_1) = (k1_xboole_0))) | (((sk_C_1) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('simplify', [status(thm)], ['191'])).
% 6.85/7.08  thf('193', plain,
% 6.85/7.08      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 6.85/7.08      inference('split', [status(esa)], ['59'])).
% 6.85/7.08  thf('194', plain, ($false),
% 6.85/7.08      inference('sat_resolution*', [status(thm)],
% 6.85/7.08                ['62', '63', '65', '156', '192', '193'])).
% 6.85/7.08  
% 6.85/7.08  % SZS output end Refutation
% 6.85/7.08  
% 6.85/7.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
