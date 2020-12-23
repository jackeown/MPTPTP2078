%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UgtAWbWfV9

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:43 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 142 expanded)
%              Number of leaves         :   17 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  654 (1283 expanded)
%              Number of equality atoms :   27 (  41 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

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
    ! [X12: $i] :
      ( ( r2_hidden @ sk_C @ sk_A_1 )
      | ~ ( r2_hidden @ X12 @ sk_A_1 )
      | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A_1 )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) )
    | ( r2_hidden @ sk_C @ sk_A_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X12: $i] :
      ( ( r2_hidden @ sk_C @ sk_B_1 )
      | ~ ( r2_hidden @ X12 @ sk_A_1 )
      | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_C @ sk_B_1 )
    | ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A_1 )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X12: $i] :
      ( ( r1_xboole_0 @ sk_A_1 @ sk_B_1 )
      | ~ ( r2_hidden @ X12 @ sk_A_1 )
      | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_xboole_0 @ sk_A_1 @ sk_B_1 )
    | ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A_1 )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ sk_C @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r2_hidden @ sk_C @ sk_B_1 )
   <= ( r2_hidden @ sk_C @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_C @ sk_A_1 )
    | ~ ( r1_xboole_0 @ sk_A_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_C @ sk_A_1 )
   <= ( r2_hidden @ sk_C @ sk_A_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A_1 )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A_1 )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B_1 )
   <= ( ( r2_hidden @ sk_C @ sk_A_1 )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A_1 )
          | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B_1 )
    | ~ ( r2_hidden @ sk_C @ sk_A_1 )
    | ~ ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A_1 )
          | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_C @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('14',plain,
    ( ( r1_xboole_0 @ sk_A_1 @ sk_B_1 )
   <= ( r1_xboole_0 @ sk_A_1 @ sk_B_1 ) ),
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

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k3_xboole_0 @ sk_A_1 @ sk_B_1 )
      = o_0_0_xboole_0 )
   <= ( r1_xboole_0 @ sk_A_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_C @ sk_A_1 )
   <= ( r2_hidden @ sk_C @ sk_A_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('20',plain,
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

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ( r2_hidden @ X3 @ X6 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_C @ X0 )
        | ( r2_hidden @ sk_C @ ( k3_xboole_0 @ X0 @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_C @ ( k3_xboole_0 @ sk_A_1 @ sk_B_1 ) )
   <= ( ( r2_hidden @ sk_C @ sk_A_1 )
      & ( r2_hidden @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,
    ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A_1 @ sk_B_1 ) )
   <= ( ( r2_hidden @ sk_C @ sk_A_1 )
      & ( r2_hidden @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
   <= ( ( r1_xboole_0 @ sk_A_1 @ sk_B_1 )
      & ( r2_hidden @ sk_C @ sk_A_1 )
      & ( r2_hidden @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('28',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A_1 @ sk_B_1 )
    | ~ ( r2_hidden @ sk_C @ sk_A_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r1_xboole_0 @ sk_A_1 @ sk_B_1 )
    | ( r2_hidden @ sk_C @ sk_A_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('31',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('33',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('37',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A_1 )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A_1 )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A_1 @ X0 ) )
        | ~ ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ sk_A_1 @ X0 ) ) @ sk_B_1 ) )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A_1 )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A_1 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A_1 @ sk_B_1 ) ) )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A_1 )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A_1 @ sk_B_1 ) )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A_1 )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k3_xboole_0 @ X9 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('48',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('49',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k3_xboole_0 @ X9 @ X11 )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X1: $i] :
      ( ( r1_xboole_0 @ X1 @ o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('53',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ o_0_0_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ( X2
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k3_xboole_0 @ sk_A_1 @ sk_B_1 )
      = o_0_0_xboole_0 )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A_1 )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','63'])).

thf('65',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k3_xboole_0 @ X9 @ X11 )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('66',plain,
    ( ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ sk_A_1 @ sk_B_1 ) )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A_1 )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_xboole_0 @ sk_A_1 @ sk_B_1 )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A_1 )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ~ ( r1_xboole_0 @ sk_A_1 @ sk_B_1 )
   <= ~ ( r1_xboole_0 @ sk_A_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('69',plain,
    ( ( r1_xboole_0 @ sk_A_1 @ sk_B_1 )
    | ~ ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A_1 )
          | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','12','13','29','30','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UgtAWbWfV9
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:56:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.70/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.89  % Solved by: fo/fo7.sh
% 0.70/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.89  % done 970 iterations in 0.426s
% 0.70/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.89  % SZS output start Refutation
% 0.70/0.89  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.70/0.89  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.70/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.70/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.89  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.70/0.89  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.89  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.70/0.89  thf(sk_B_type, type, sk_B: $i > $i).
% 0.70/0.89  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.70/0.89  thf(t3_xboole_0, conjecture,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.70/0.89            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.70/0.89       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.70/0.89            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.70/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.89    (~( ![A:$i,B:$i]:
% 0.70/0.89        ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.70/0.89               ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.70/0.89          ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.70/0.89               ( ![C:$i]:
% 0.70/0.89                 ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ) )),
% 0.70/0.89    inference('cnf.neg', [status(esa)], [t3_xboole_0])).
% 0.70/0.89  thf('0', plain,
% 0.70/0.89      (![X12 : $i]:
% 0.70/0.89         ((r2_hidden @ sk_C @ sk_A_1)
% 0.70/0.89          | ~ (r2_hidden @ X12 @ sk_A_1)
% 0.70/0.89          | ~ (r2_hidden @ X12 @ sk_B_1))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('1', plain,
% 0.70/0.89      ((![X12 : $i]:
% 0.70/0.89          (~ (r2_hidden @ X12 @ sk_A_1) | ~ (r2_hidden @ X12 @ sk_B_1))) | 
% 0.70/0.89       ((r2_hidden @ sk_C @ sk_A_1))),
% 0.70/0.89      inference('split', [status(esa)], ['0'])).
% 0.70/0.89  thf('2', plain,
% 0.70/0.89      (![X12 : $i]:
% 0.70/0.89         ((r2_hidden @ sk_C @ sk_B_1)
% 0.70/0.89          | ~ (r2_hidden @ X12 @ sk_A_1)
% 0.70/0.89          | ~ (r2_hidden @ X12 @ sk_B_1))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('3', plain,
% 0.70/0.89      (((r2_hidden @ sk_C @ sk_B_1)) | 
% 0.70/0.89       (![X12 : $i]:
% 0.70/0.89          (~ (r2_hidden @ X12 @ sk_A_1) | ~ (r2_hidden @ X12 @ sk_B_1)))),
% 0.70/0.89      inference('split', [status(esa)], ['2'])).
% 0.70/0.89  thf('4', plain,
% 0.70/0.89      (![X12 : $i]:
% 0.70/0.89         ((r1_xboole_0 @ sk_A_1 @ sk_B_1)
% 0.70/0.89          | ~ (r2_hidden @ X12 @ sk_A_1)
% 0.70/0.89          | ~ (r2_hidden @ X12 @ sk_B_1))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('5', plain,
% 0.70/0.89      (((r1_xboole_0 @ sk_A_1 @ sk_B_1)) | 
% 0.70/0.89       (![X12 : $i]:
% 0.70/0.89          (~ (r2_hidden @ X12 @ sk_A_1) | ~ (r2_hidden @ X12 @ sk_B_1)))),
% 0.70/0.89      inference('split', [status(esa)], ['4'])).
% 0.70/0.89  thf('6', plain,
% 0.70/0.89      (((r2_hidden @ sk_C @ sk_B_1) | ~ (r1_xboole_0 @ sk_A_1 @ sk_B_1))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('7', plain,
% 0.70/0.89      (((r2_hidden @ sk_C @ sk_B_1)) <= (((r2_hidden @ sk_C @ sk_B_1)))),
% 0.70/0.89      inference('split', [status(esa)], ['6'])).
% 0.70/0.89  thf('8', plain,
% 0.70/0.89      (((r2_hidden @ sk_C @ sk_A_1) | ~ (r1_xboole_0 @ sk_A_1 @ sk_B_1))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('9', plain,
% 0.70/0.89      (((r2_hidden @ sk_C @ sk_A_1)) <= (((r2_hidden @ sk_C @ sk_A_1)))),
% 0.70/0.89      inference('split', [status(esa)], ['8'])).
% 0.70/0.89  thf('10', plain,
% 0.70/0.89      ((![X12 : $i]:
% 0.70/0.89          (~ (r2_hidden @ X12 @ sk_A_1) | ~ (r2_hidden @ X12 @ sk_B_1)))
% 0.70/0.89         <= ((![X12 : $i]:
% 0.70/0.89                (~ (r2_hidden @ X12 @ sk_A_1) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.70/0.89      inference('split', [status(esa)], ['0'])).
% 0.70/0.89  thf('11', plain,
% 0.70/0.89      ((~ (r2_hidden @ sk_C @ sk_B_1))
% 0.70/0.89         <= (((r2_hidden @ sk_C @ sk_A_1)) & 
% 0.70/0.89             (![X12 : $i]:
% 0.70/0.89                (~ (r2_hidden @ X12 @ sk_A_1) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['9', '10'])).
% 0.70/0.89  thf('12', plain,
% 0.70/0.89      (~ ((r2_hidden @ sk_C @ sk_B_1)) | ~ ((r2_hidden @ sk_C @ sk_A_1)) | 
% 0.70/0.89       ~
% 0.70/0.89       (![X12 : $i]:
% 0.70/0.89          (~ (r2_hidden @ X12 @ sk_A_1) | ~ (r2_hidden @ X12 @ sk_B_1)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['7', '11'])).
% 0.70/0.89  thf('13', plain,
% 0.70/0.89      (((r2_hidden @ sk_C @ sk_B_1)) | ~ ((r1_xboole_0 @ sk_A_1 @ sk_B_1))),
% 0.70/0.89      inference('split', [status(esa)], ['6'])).
% 0.70/0.89  thf('14', plain,
% 0.70/0.89      (((r1_xboole_0 @ sk_A_1 @ sk_B_1)) <= (((r1_xboole_0 @ sk_A_1 @ sk_B_1)))),
% 0.70/0.89      inference('split', [status(esa)], ['4'])).
% 0.70/0.89  thf(d7_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.70/0.89       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.70/0.89  thf('15', plain,
% 0.70/0.89      (![X9 : $i, X10 : $i]:
% 0.70/0.89         (((k3_xboole_0 @ X9 @ X10) = (k1_xboole_0))
% 0.70/0.89          | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.70/0.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.89  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.70/0.89  thf('16', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.70/0.89      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.70/0.89  thf('17', plain,
% 0.70/0.89      (![X9 : $i, X10 : $i]:
% 0.70/0.89         (((k3_xboole_0 @ X9 @ X10) = (o_0_0_xboole_0))
% 0.70/0.89          | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.70/0.89      inference('demod', [status(thm)], ['15', '16'])).
% 0.70/0.89  thf('18', plain,
% 0.70/0.89      ((((k3_xboole_0 @ sk_A_1 @ sk_B_1) = (o_0_0_xboole_0)))
% 0.70/0.89         <= (((r1_xboole_0 @ sk_A_1 @ sk_B_1)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['14', '17'])).
% 0.70/0.89  thf('19', plain,
% 0.70/0.89      (((r2_hidden @ sk_C @ sk_A_1)) <= (((r2_hidden @ sk_C @ sk_A_1)))),
% 0.70/0.89      inference('split', [status(esa)], ['8'])).
% 0.70/0.89  thf('20', plain,
% 0.70/0.89      (((r2_hidden @ sk_C @ sk_B_1)) <= (((r2_hidden @ sk_C @ sk_B_1)))),
% 0.70/0.89      inference('split', [status(esa)], ['6'])).
% 0.70/0.89  thf(d4_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.70/0.89       ( ![D:$i]:
% 0.70/0.89         ( ( r2_hidden @ D @ C ) <=>
% 0.70/0.89           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.70/0.89  thf('21', plain,
% 0.70/0.89      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X3 @ X4)
% 0.70/0.89          | ~ (r2_hidden @ X3 @ X5)
% 0.70/0.89          | (r2_hidden @ X3 @ X6)
% 0.70/0.89          | ((X6) != (k3_xboole_0 @ X4 @ X5)))),
% 0.70/0.89      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.70/0.89  thf('22', plain,
% 0.70/0.89      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.70/0.89         ((r2_hidden @ X3 @ (k3_xboole_0 @ X4 @ X5))
% 0.70/0.89          | ~ (r2_hidden @ X3 @ X5)
% 0.70/0.89          | ~ (r2_hidden @ X3 @ X4))),
% 0.70/0.89      inference('simplify', [status(thm)], ['21'])).
% 0.70/0.89  thf('23', plain,
% 0.70/0.89      ((![X0 : $i]:
% 0.70/0.89          (~ (r2_hidden @ sk_C @ X0)
% 0.70/0.89           | (r2_hidden @ sk_C @ (k3_xboole_0 @ X0 @ sk_B_1))))
% 0.70/0.89         <= (((r2_hidden @ sk_C @ sk_B_1)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['20', '22'])).
% 0.70/0.89  thf('24', plain,
% 0.70/0.89      (((r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A_1 @ sk_B_1)))
% 0.70/0.89         <= (((r2_hidden @ sk_C @ sk_A_1)) & ((r2_hidden @ sk_C @ sk_B_1)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['19', '23'])).
% 0.70/0.89  thf(d1_xboole_0, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.70/0.89  thf('25', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.89  thf('26', plain,
% 0.70/0.89      ((~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A_1 @ sk_B_1)))
% 0.70/0.89         <= (((r2_hidden @ sk_C @ sk_A_1)) & ((r2_hidden @ sk_C @ sk_B_1)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['24', '25'])).
% 0.70/0.89  thf('27', plain,
% 0.70/0.89      ((~ (v1_xboole_0 @ o_0_0_xboole_0))
% 0.70/0.89         <= (((r1_xboole_0 @ sk_A_1 @ sk_B_1)) & 
% 0.70/0.89             ((r2_hidden @ sk_C @ sk_A_1)) & 
% 0.70/0.89             ((r2_hidden @ sk_C @ sk_B_1)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['18', '26'])).
% 0.70/0.89  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 0.70/0.89  thf('28', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.70/0.89      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.70/0.89  thf('29', plain,
% 0.70/0.89      (~ ((r2_hidden @ sk_C @ sk_B_1)) | ~ ((r1_xboole_0 @ sk_A_1 @ sk_B_1)) | 
% 0.70/0.89       ~ ((r2_hidden @ sk_C @ sk_A_1))),
% 0.70/0.89      inference('demod', [status(thm)], ['27', '28'])).
% 0.70/0.89  thf('30', plain,
% 0.70/0.89      (~ ((r1_xboole_0 @ sk_A_1 @ sk_B_1)) | ((r2_hidden @ sk_C @ sk_A_1))),
% 0.70/0.89      inference('split', [status(esa)], ['8'])).
% 0.70/0.89  thf('31', plain,
% 0.70/0.89      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.70/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.89  thf('32', plain,
% 0.70/0.89      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X7 @ X6)
% 0.70/0.89          | (r2_hidden @ X7 @ X5)
% 0.70/0.89          | ((X6) != (k3_xboole_0 @ X4 @ X5)))),
% 0.70/0.89      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.70/0.89  thf('33', plain,
% 0.70/0.89      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.70/0.89         ((r2_hidden @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.70/0.89      inference('simplify', [status(thm)], ['32'])).
% 0.70/0.89  thf('34', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 0.70/0.89          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['31', '33'])).
% 0.70/0.89  thf('35', plain,
% 0.70/0.89      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.70/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.89  thf('36', plain,
% 0.70/0.89      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X7 @ X6)
% 0.70/0.89          | (r2_hidden @ X7 @ X4)
% 0.70/0.89          | ((X6) != (k3_xboole_0 @ X4 @ X5)))),
% 0.70/0.89      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.70/0.89  thf('37', plain,
% 0.70/0.89      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.70/0.89         ((r2_hidden @ X7 @ X4) | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.70/0.89      inference('simplify', [status(thm)], ['36'])).
% 0.70/0.89  thf('38', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 0.70/0.89          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['35', '37'])).
% 0.70/0.89  thf('39', plain,
% 0.70/0.89      ((![X12 : $i]:
% 0.70/0.89          (~ (r2_hidden @ X12 @ sk_A_1) | ~ (r2_hidden @ X12 @ sk_B_1)))
% 0.70/0.89         <= ((![X12 : $i]:
% 0.70/0.89                (~ (r2_hidden @ X12 @ sk_A_1) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.70/0.89      inference('split', [status(esa)], ['0'])).
% 0.70/0.89  thf('40', plain,
% 0.70/0.89      ((![X0 : $i]:
% 0.70/0.89          ((v1_xboole_0 @ (k3_xboole_0 @ sk_A_1 @ X0))
% 0.70/0.89           | ~ (r2_hidden @ (sk_B @ (k3_xboole_0 @ sk_A_1 @ X0)) @ sk_B_1)))
% 0.70/0.89         <= ((![X12 : $i]:
% 0.70/0.89                (~ (r2_hidden @ X12 @ sk_A_1) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['38', '39'])).
% 0.70/0.89  thf('41', plain,
% 0.70/0.89      ((((v1_xboole_0 @ (k3_xboole_0 @ sk_A_1 @ sk_B_1))
% 0.70/0.89         | (v1_xboole_0 @ (k3_xboole_0 @ sk_A_1 @ sk_B_1))))
% 0.70/0.89         <= ((![X12 : $i]:
% 0.70/0.89                (~ (r2_hidden @ X12 @ sk_A_1) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['34', '40'])).
% 0.70/0.89  thf('42', plain,
% 0.70/0.89      (((v1_xboole_0 @ (k3_xboole_0 @ sk_A_1 @ sk_B_1)))
% 0.70/0.89         <= ((![X12 : $i]:
% 0.70/0.89                (~ (r2_hidden @ X12 @ sk_A_1) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.70/0.89      inference('simplify', [status(thm)], ['41'])).
% 0.70/0.89  thf('43', plain,
% 0.70/0.89      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.70/0.89         (((X8) = (k3_xboole_0 @ X4 @ X5))
% 0.70/0.89          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X5)
% 0.70/0.89          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.70/0.89      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.70/0.89  thf('44', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.70/0.89          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.70/0.89      inference('eq_fact', [status(thm)], ['43'])).
% 0.70/0.89  thf('45', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.89  thf('46', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (((X0) = (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['44', '45'])).
% 0.70/0.89  thf('47', plain,
% 0.70/0.89      (![X9 : $i, X11 : $i]:
% 0.70/0.89         ((r1_xboole_0 @ X9 @ X11)
% 0.70/0.89          | ((k3_xboole_0 @ X9 @ X11) != (k1_xboole_0)))),
% 0.70/0.89      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.89  thf('48', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.70/0.89      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.70/0.89  thf('49', plain,
% 0.70/0.89      (![X9 : $i, X11 : $i]:
% 0.70/0.89         ((r1_xboole_0 @ X9 @ X11)
% 0.70/0.89          | ((k3_xboole_0 @ X9 @ X11) != (o_0_0_xboole_0)))),
% 0.70/0.89      inference('demod', [status(thm)], ['47', '48'])).
% 0.70/0.89  thf('50', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (((X0) != (o_0_0_xboole_0))
% 0.70/0.89          | ~ (v1_xboole_0 @ X0)
% 0.70/0.89          | (r1_xboole_0 @ X1 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['46', '49'])).
% 0.70/0.89  thf('51', plain,
% 0.70/0.89      (![X1 : $i]:
% 0.70/0.89         ((r1_xboole_0 @ X1 @ o_0_0_xboole_0)
% 0.70/0.89          | ~ (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.70/0.89      inference('simplify', [status(thm)], ['50'])).
% 0.70/0.89  thf('52', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.70/0.89      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.70/0.89  thf('53', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ o_0_0_xboole_0)),
% 0.70/0.89      inference('simplify_reflect+', [status(thm)], ['51', '52'])).
% 0.70/0.89  thf('54', plain,
% 0.70/0.89      (![X9 : $i, X10 : $i]:
% 0.70/0.89         (((k3_xboole_0 @ X9 @ X10) = (o_0_0_xboole_0))
% 0.70/0.89          | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.70/0.89      inference('demod', [status(thm)], ['15', '16'])).
% 0.70/0.89  thf('55', plain,
% 0.70/0.89      (![X0 : $i]: ((k3_xboole_0 @ X0 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['53', '54'])).
% 0.70/0.89  thf('56', plain,
% 0.70/0.89      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.70/0.89         (((X8) = (k3_xboole_0 @ X4 @ X5))
% 0.70/0.89          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X5)
% 0.70/0.89          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.70/0.89      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.70/0.89  thf('57', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.89  thf('58', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         ((r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X2)
% 0.70/0.89          | ((X2) = (k3_xboole_0 @ X1 @ X0))
% 0.70/0.89          | ~ (v1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['56', '57'])).
% 0.70/0.89  thf('59', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.70/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.70/0.89  thf('60', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (~ (v1_xboole_0 @ X2)
% 0.70/0.89          | ((X0) = (k3_xboole_0 @ X1 @ X2))
% 0.70/0.89          | ~ (v1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['58', '59'])).
% 0.70/0.89  thf('61', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (((X0) = (o_0_0_xboole_0))
% 0.70/0.89          | ~ (v1_xboole_0 @ X0)
% 0.70/0.89          | ~ (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['55', '60'])).
% 0.70/0.89  thf('62', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.70/0.89      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.70/0.89  thf('63', plain,
% 0.70/0.89      (![X0 : $i]: (((X0) = (o_0_0_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['61', '62'])).
% 0.70/0.89  thf('64', plain,
% 0.70/0.89      ((((k3_xboole_0 @ sk_A_1 @ sk_B_1) = (o_0_0_xboole_0)))
% 0.70/0.89         <= ((![X12 : $i]:
% 0.70/0.89                (~ (r2_hidden @ X12 @ sk_A_1) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['42', '63'])).
% 0.70/0.89  thf('65', plain,
% 0.70/0.89      (![X9 : $i, X11 : $i]:
% 0.70/0.89         ((r1_xboole_0 @ X9 @ X11)
% 0.70/0.89          | ((k3_xboole_0 @ X9 @ X11) != (o_0_0_xboole_0)))),
% 0.70/0.89      inference('demod', [status(thm)], ['47', '48'])).
% 0.70/0.89  thf('66', plain,
% 0.70/0.89      (((((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.70/0.89         | (r1_xboole_0 @ sk_A_1 @ sk_B_1)))
% 0.70/0.89         <= ((![X12 : $i]:
% 0.70/0.89                (~ (r2_hidden @ X12 @ sk_A_1) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['64', '65'])).
% 0.70/0.89  thf('67', plain,
% 0.70/0.89      (((r1_xboole_0 @ sk_A_1 @ sk_B_1))
% 0.70/0.89         <= ((![X12 : $i]:
% 0.70/0.89                (~ (r2_hidden @ X12 @ sk_A_1) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.70/0.89      inference('simplify', [status(thm)], ['66'])).
% 0.70/0.89  thf('68', plain,
% 0.70/0.89      ((~ (r1_xboole_0 @ sk_A_1 @ sk_B_1))
% 0.70/0.89         <= (~ ((r1_xboole_0 @ sk_A_1 @ sk_B_1)))),
% 0.70/0.89      inference('split', [status(esa)], ['8'])).
% 0.70/0.89  thf('69', plain,
% 0.70/0.89      (((r1_xboole_0 @ sk_A_1 @ sk_B_1)) | 
% 0.70/0.89       ~
% 0.70/0.89       (![X12 : $i]:
% 0.70/0.89          (~ (r2_hidden @ X12 @ sk_A_1) | ~ (r2_hidden @ X12 @ sk_B_1)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['67', '68'])).
% 0.70/0.89  thf('70', plain, ($false),
% 0.70/0.89      inference('sat_resolution*', [status(thm)],
% 0.70/0.89                ['1', '3', '5', '12', '13', '29', '30', '69'])).
% 0.70/0.89  
% 0.70/0.89  % SZS output end Refutation
% 0.70/0.89  
% 0.70/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
