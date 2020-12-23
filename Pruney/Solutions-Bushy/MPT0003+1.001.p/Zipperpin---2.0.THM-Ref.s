%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0003+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hB62hcHnFK

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:09 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 138 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :  644 (1267 expanded)
%              Number of equality atoms :   28 (  41 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t3_xboole_0,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( ? [C: $i] :
                ( ( r2_hidden @ C @ B )
                & ( r2_hidden @ C @ A ) )
            & ( r1_xboole_0 @ A @ B ) )
        & ~ ( ~ ( r1_xboole_0 @ A @ B )
            & ! [C: $i] :
                ~ ( ( r2_hidden @ C @ A )
                  & ( r2_hidden @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_xboole_0])).

thf('0',plain,(
    ! [X13: $i] :
      ( ( r2_hidden @ sk_C @ sk_A )
      | ~ ( r2_hidden @ X13 @ sk_A )
      | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_B_1 ) )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X13: $i] :
      ( ( r2_hidden @ sk_C @ sk_B_1 )
      | ~ ( r2_hidden @ X13 @ sk_A )
      | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_C @ sk_B_1 )
    | ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X13: $i] :
      ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X13 @ sk_A )
      | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_C @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r2_hidden @ sk_C @ sk_B_1 )
   <= ( r2_hidden @ sk_C @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_C @ sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_C @ sk_A )
   <= ( r2_hidden @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_B_1 ) )
   <= ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B_1 )
   <= ( ( r2_hidden @ sk_C @ sk_A )
      & ! [X13: $i] :
          ( ~ ( r2_hidden @ X13 @ sk_A )
          | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B_1 )
    | ~ ( r2_hidden @ sk_C @ sk_A )
    | ~ ! [X13: $i] :
          ( ~ ( r2_hidden @ X13 @ sk_A )
          | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_C @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_C @ sk_A )
   <= ( r2_hidden @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('18',plain,
    ( ( r2_hidden @ sk_C @ sk_B_1 )
   <= ( r2_hidden @ sk_C @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ( r2_hidden @ X3 @ X6 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_C @ X0 )
        | ( r2_hidden @ sk_C @ ( k3_xboole_0 @ X0 @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( ( r2_hidden @ sk_C @ sk_A )
      & ( r2_hidden @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_C @ k1_xboole_0 )
   <= ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_C @ sk_A )
      & ( r2_hidden @ sk_C @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['16','22'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_C @ sk_A )
      & ( r2_hidden @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('27',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('29',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('33',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('34',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k3_xboole_0 @ X9 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ( ( r1_xboole_0 @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['26','29'])).

thf('42',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('46',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['48'])).

thf('50',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('51',plain,
    ( ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_B_1 ) )
   <= ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_A ) @ X1 )
        | ( X1
          = ( k3_xboole_0 @ sk_A @ X0 ) )
        | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 @ sk_A ) @ sk_B_1 ) )
   <= ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k1_xboole_0
        = ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 ) )
   <= ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_B_1 @ sk_A ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) )
   <= ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('56',plain,
    ( ( ( k1_xboole_0
        = ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['26','29'])).

thf('58',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k3_xboole_0 @ X9 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('60',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ! [X13: $i] :
        ( ~ ( r2_hidden @ X13 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('63',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ~ ! [X13: $i] :
          ( ~ ( r2_hidden @ X13 @ sk_A )
          | ~ ( r2_hidden @ X13 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','12','13','31','32','63'])).


%------------------------------------------------------------------------------
