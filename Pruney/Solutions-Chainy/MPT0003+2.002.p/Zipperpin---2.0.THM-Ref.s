%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T84fNXWADr

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:43 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 129 expanded)
%              Number of leaves         :   15 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  629 (1227 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
      ( ( r2_hidden @ sk_C @ sk_A )
      | ~ ( r2_hidden @ X12 @ sk_A )
      | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X12: $i] :
      ( ( r2_hidden @ sk_C @ sk_B_1 )
      | ~ ( r2_hidden @ X12 @ sk_A )
      | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_C @ sk_B_1 )
    | ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X12: $i] :
      ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X12 @ sk_A )
      | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
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
    ( ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B_1 )
   <= ( ( r2_hidden @ sk_C @ sk_A )
      & ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B_1 )
    | ~ ( r2_hidden @ sk_C @ sk_A )
    | ~ ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( ( r2_hidden @ sk_C @ sk_A )
      & ( r2_hidden @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_C @ sk_A )
      & ( r2_hidden @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('29',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('30',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('31',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X4 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('35',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) )
        | ~ ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) @ sk_B_1 ) )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k3_xboole_0 @ X9 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X1: $i] :
      ( ( r1_xboole_0 @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ( X2
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','59'])).

thf('61',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k3_xboole_0 @ X9 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('62',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ! [X12: $i] :
        ( ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('65',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B_1 )
    | ~ ! [X12: $i] :
          ( ~ ( r2_hidden @ X12 @ sk_A )
          | ~ ( r2_hidden @ X12 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','12','13','27','28','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T84fNXWADr
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:26:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.74/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.74/0.93  % Solved by: fo/fo7.sh
% 0.74/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.93  % done 1276 iterations in 0.474s
% 0.74/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.74/0.93  % SZS output start Refutation
% 0.74/0.93  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.74/0.93  thf(sk_C_type, type, sk_C: $i).
% 0.74/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.74/0.93  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.74/0.93  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.74/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.93  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.74/0.93  thf(sk_B_type, type, sk_B: $i > $i).
% 0.74/0.93  thf(t3_xboole_0, conjecture,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.74/0.93            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.74/0.93       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.74/0.93            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.74/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.93    (~( ![A:$i,B:$i]:
% 0.74/0.93        ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.74/0.93               ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.74/0.93          ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.74/0.93               ( ![C:$i]:
% 0.74/0.93                 ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ) )),
% 0.74/0.93    inference('cnf.neg', [status(esa)], [t3_xboole_0])).
% 0.74/0.93  thf('0', plain,
% 0.74/0.93      (![X12 : $i]:
% 0.74/0.93         ((r2_hidden @ sk_C @ sk_A)
% 0.74/0.93          | ~ (r2_hidden @ X12 @ sk_A)
% 0.74/0.93          | ~ (r2_hidden @ X12 @ sk_B_1))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('1', plain,
% 0.74/0.93      ((![X12 : $i]:
% 0.74/0.93          (~ (r2_hidden @ X12 @ sk_A) | ~ (r2_hidden @ X12 @ sk_B_1))) | 
% 0.74/0.93       ((r2_hidden @ sk_C @ sk_A))),
% 0.74/0.93      inference('split', [status(esa)], ['0'])).
% 0.74/0.93  thf('2', plain,
% 0.74/0.93      (![X12 : $i]:
% 0.74/0.93         ((r2_hidden @ sk_C @ sk_B_1)
% 0.74/0.93          | ~ (r2_hidden @ X12 @ sk_A)
% 0.74/0.93          | ~ (r2_hidden @ X12 @ sk_B_1))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('3', plain,
% 0.74/0.93      (((r2_hidden @ sk_C @ sk_B_1)) | 
% 0.74/0.93       (![X12 : $i]:
% 0.74/0.93          (~ (r2_hidden @ X12 @ sk_A) | ~ (r2_hidden @ X12 @ sk_B_1)))),
% 0.74/0.93      inference('split', [status(esa)], ['2'])).
% 0.74/0.93  thf('4', plain,
% 0.74/0.93      (![X12 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ sk_A @ sk_B_1)
% 0.74/0.93          | ~ (r2_hidden @ X12 @ sk_A)
% 0.74/0.93          | ~ (r2_hidden @ X12 @ sk_B_1))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('5', plain,
% 0.74/0.93      (((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 0.74/0.93       (![X12 : $i]:
% 0.74/0.93          (~ (r2_hidden @ X12 @ sk_A) | ~ (r2_hidden @ X12 @ sk_B_1)))),
% 0.74/0.93      inference('split', [status(esa)], ['4'])).
% 0.74/0.93  thf('6', plain,
% 0.74/0.93      (((r2_hidden @ sk_C @ sk_B_1) | ~ (r1_xboole_0 @ sk_A @ sk_B_1))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('7', plain,
% 0.74/0.93      (((r2_hidden @ sk_C @ sk_B_1)) <= (((r2_hidden @ sk_C @ sk_B_1)))),
% 0.74/0.93      inference('split', [status(esa)], ['6'])).
% 0.74/0.93  thf('8', plain,
% 0.74/0.93      (((r2_hidden @ sk_C @ sk_A) | ~ (r1_xboole_0 @ sk_A @ sk_B_1))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('9', plain,
% 0.74/0.93      (((r2_hidden @ sk_C @ sk_A)) <= (((r2_hidden @ sk_C @ sk_A)))),
% 0.74/0.93      inference('split', [status(esa)], ['8'])).
% 0.74/0.93  thf('10', plain,
% 0.74/0.93      ((![X12 : $i]:
% 0.74/0.93          (~ (r2_hidden @ X12 @ sk_A) | ~ (r2_hidden @ X12 @ sk_B_1)))
% 0.74/0.93         <= ((![X12 : $i]:
% 0.74/0.93                (~ (r2_hidden @ X12 @ sk_A) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.74/0.93      inference('split', [status(esa)], ['0'])).
% 0.74/0.93  thf('11', plain,
% 0.74/0.93      ((~ (r2_hidden @ sk_C @ sk_B_1))
% 0.74/0.93         <= (((r2_hidden @ sk_C @ sk_A)) & 
% 0.74/0.93             (![X12 : $i]:
% 0.74/0.93                (~ (r2_hidden @ X12 @ sk_A) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['9', '10'])).
% 0.74/0.93  thf('12', plain,
% 0.74/0.93      (~ ((r2_hidden @ sk_C @ sk_B_1)) | ~ ((r2_hidden @ sk_C @ sk_A)) | 
% 0.74/0.93       ~
% 0.74/0.93       (![X12 : $i]:
% 0.74/0.93          (~ (r2_hidden @ X12 @ sk_A) | ~ (r2_hidden @ X12 @ sk_B_1)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['7', '11'])).
% 0.74/0.93  thf('13', plain,
% 0.74/0.93      (((r2_hidden @ sk_C @ sk_B_1)) | ~ ((r1_xboole_0 @ sk_A @ sk_B_1))),
% 0.74/0.93      inference('split', [status(esa)], ['6'])).
% 0.74/0.93  thf('14', plain,
% 0.74/0.93      (((r1_xboole_0 @ sk_A @ sk_B_1)) <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 0.74/0.93      inference('split', [status(esa)], ['4'])).
% 0.74/0.93  thf(d7_xboole_0, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.74/0.93       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.74/0.93  thf('15', plain,
% 0.74/0.93      (![X9 : $i, X10 : $i]:
% 0.74/0.93         (((k3_xboole_0 @ X9 @ X10) = (k1_xboole_0))
% 0.74/0.93          | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.74/0.93      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.74/0.93  thf('16', plain,
% 0.74/0.93      ((((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.74/0.93         <= (((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['14', '15'])).
% 0.74/0.93  thf('17', plain,
% 0.74/0.93      (((r2_hidden @ sk_C @ sk_A)) <= (((r2_hidden @ sk_C @ sk_A)))),
% 0.74/0.93      inference('split', [status(esa)], ['8'])).
% 0.74/0.93  thf('18', plain,
% 0.74/0.93      (((r2_hidden @ sk_C @ sk_B_1)) <= (((r2_hidden @ sk_C @ sk_B_1)))),
% 0.74/0.93      inference('split', [status(esa)], ['6'])).
% 0.74/0.93  thf(d4_xboole_0, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.74/0.93       ( ![D:$i]:
% 0.74/0.93         ( ( r2_hidden @ D @ C ) <=>
% 0.74/0.93           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.74/0.93  thf('19', plain,
% 0.74/0.93      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X3 @ X4)
% 0.74/0.93          | ~ (r2_hidden @ X3 @ X5)
% 0.74/0.93          | (r2_hidden @ X3 @ X6)
% 0.74/0.93          | ((X6) != (k3_xboole_0 @ X4 @ X5)))),
% 0.74/0.93      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.74/0.93  thf('20', plain,
% 0.74/0.93      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.74/0.93         ((r2_hidden @ X3 @ (k3_xboole_0 @ X4 @ X5))
% 0.74/0.93          | ~ (r2_hidden @ X3 @ X5)
% 0.74/0.93          | ~ (r2_hidden @ X3 @ X4))),
% 0.74/0.93      inference('simplify', [status(thm)], ['19'])).
% 0.74/0.93  thf('21', plain,
% 0.74/0.93      ((![X0 : $i]:
% 0.74/0.93          (~ (r2_hidden @ sk_C @ X0)
% 0.74/0.93           | (r2_hidden @ sk_C @ (k3_xboole_0 @ X0 @ sk_B_1))))
% 0.74/0.93         <= (((r2_hidden @ sk_C @ sk_B_1)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['18', '20'])).
% 0.74/0.93  thf('22', plain,
% 0.74/0.93      (((r2_hidden @ sk_C @ (k3_xboole_0 @ sk_A @ sk_B_1)))
% 0.74/0.93         <= (((r2_hidden @ sk_C @ sk_A)) & ((r2_hidden @ sk_C @ sk_B_1)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['17', '21'])).
% 0.74/0.93  thf(d1_xboole_0, axiom,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.74/0.93  thf('23', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.74/0.93      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.93  thf('24', plain,
% 0.74/0.93      ((~ (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1)))
% 0.74/0.93         <= (((r2_hidden @ sk_C @ sk_A)) & ((r2_hidden @ sk_C @ sk_B_1)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['22', '23'])).
% 0.74/0.93  thf('25', plain,
% 0.74/0.93      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.74/0.93         <= (((r1_xboole_0 @ sk_A @ sk_B_1)) & 
% 0.74/0.93             ((r2_hidden @ sk_C @ sk_A)) & 
% 0.74/0.93             ((r2_hidden @ sk_C @ sk_B_1)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['16', '24'])).
% 0.74/0.93  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.74/0.93  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.74/0.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.74/0.93  thf('27', plain,
% 0.74/0.93      (~ ((r2_hidden @ sk_C @ sk_B_1)) | ~ ((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 0.74/0.93       ~ ((r2_hidden @ sk_C @ sk_A))),
% 0.74/0.93      inference('demod', [status(thm)], ['25', '26'])).
% 0.74/0.93  thf('28', plain,
% 0.74/0.93      (~ ((r1_xboole_0 @ sk_A @ sk_B_1)) | ((r2_hidden @ sk_C @ sk_A))),
% 0.74/0.93      inference('split', [status(esa)], ['8'])).
% 0.74/0.93  thf('29', plain,
% 0.74/0.93      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.74/0.93      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.93  thf('30', plain,
% 0.74/0.93      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X7 @ X6)
% 0.74/0.93          | (r2_hidden @ X7 @ X5)
% 0.74/0.93          | ((X6) != (k3_xboole_0 @ X4 @ X5)))),
% 0.74/0.93      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.74/0.93  thf('31', plain,
% 0.74/0.93      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.74/0.93         ((r2_hidden @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.74/0.93      inference('simplify', [status(thm)], ['30'])).
% 0.74/0.93  thf('32', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 0.74/0.93          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['29', '31'])).
% 0.74/0.93  thf('33', plain,
% 0.74/0.93      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.74/0.93      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.93  thf('34', plain,
% 0.74/0.93      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X7 @ X6)
% 0.74/0.93          | (r2_hidden @ X7 @ X4)
% 0.74/0.93          | ((X6) != (k3_xboole_0 @ X4 @ X5)))),
% 0.74/0.93      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.74/0.93  thf('35', plain,
% 0.74/0.93      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.74/0.93         ((r2_hidden @ X7 @ X4) | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.74/0.93      inference('simplify', [status(thm)], ['34'])).
% 0.74/0.93  thf('36', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 0.74/0.93          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.74/0.93      inference('sup-', [status(thm)], ['33', '35'])).
% 0.74/0.93  thf('37', plain,
% 0.74/0.93      ((![X12 : $i]:
% 0.74/0.93          (~ (r2_hidden @ X12 @ sk_A) | ~ (r2_hidden @ X12 @ sk_B_1)))
% 0.74/0.93         <= ((![X12 : $i]:
% 0.74/0.93                (~ (r2_hidden @ X12 @ sk_A) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.74/0.93      inference('split', [status(esa)], ['0'])).
% 0.74/0.93  thf('38', plain,
% 0.74/0.93      ((![X0 : $i]:
% 0.74/0.93          ((v1_xboole_0 @ (k3_xboole_0 @ sk_A @ X0))
% 0.74/0.93           | ~ (r2_hidden @ (sk_B @ (k3_xboole_0 @ sk_A @ X0)) @ sk_B_1)))
% 0.74/0.93         <= ((![X12 : $i]:
% 0.74/0.93                (~ (r2_hidden @ X12 @ sk_A) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['36', '37'])).
% 0.74/0.93  thf('39', plain,
% 0.74/0.93      ((((v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1))
% 0.74/0.93         | (v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1))))
% 0.74/0.93         <= ((![X12 : $i]:
% 0.74/0.93                (~ (r2_hidden @ X12 @ sk_A) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['32', '38'])).
% 0.74/0.93  thf('40', plain,
% 0.74/0.93      (((v1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1)))
% 0.74/0.93         <= ((![X12 : $i]:
% 0.74/0.93                (~ (r2_hidden @ X12 @ sk_A) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.74/0.93      inference('simplify', [status(thm)], ['39'])).
% 0.74/0.93  thf('41', plain,
% 0.74/0.93      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.74/0.93         (((X8) = (k3_xboole_0 @ X4 @ X5))
% 0.74/0.93          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X5)
% 0.74/0.93          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.74/0.93      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.74/0.93  thf('42', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.74/0.93          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.74/0.93      inference('eq_fact', [status(thm)], ['41'])).
% 0.74/0.93  thf('43', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.74/0.93      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.93  thf('44', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         (((X0) = (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['42', '43'])).
% 0.74/0.93  thf('45', plain,
% 0.74/0.93      (![X9 : $i, X11 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ X9 @ X11)
% 0.74/0.93          | ((k3_xboole_0 @ X9 @ X11) != (k1_xboole_0)))),
% 0.74/0.93      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.74/0.93  thf('46', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         (((X0) != (k1_xboole_0))
% 0.74/0.93          | ~ (v1_xboole_0 @ X0)
% 0.74/0.93          | (r1_xboole_0 @ X1 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['44', '45'])).
% 0.74/0.93  thf('47', plain,
% 0.74/0.93      (![X1 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ X1 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.74/0.93      inference('simplify', [status(thm)], ['46'])).
% 0.74/0.93  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.74/0.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.74/0.93  thf('49', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.74/0.93      inference('simplify_reflect+', [status(thm)], ['47', '48'])).
% 0.74/0.93  thf('50', plain,
% 0.74/0.93      (![X9 : $i, X10 : $i]:
% 0.74/0.93         (((k3_xboole_0 @ X9 @ X10) = (k1_xboole_0))
% 0.74/0.93          | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.74/0.93      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.74/0.93  thf('51', plain,
% 0.74/0.93      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['49', '50'])).
% 0.74/0.93  thf('52', plain,
% 0.74/0.93      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.74/0.93         (((X8) = (k3_xboole_0 @ X4 @ X5))
% 0.74/0.93          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X5)
% 0.74/0.93          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.74/0.93      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.74/0.93  thf('53', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.74/0.93      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.93  thf('54', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.93         ((r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X2)
% 0.74/0.93          | ((X2) = (k3_xboole_0 @ X1 @ X0))
% 0.74/0.93          | ~ (v1_xboole_0 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['52', '53'])).
% 0.74/0.93  thf('55', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.74/0.93      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.74/0.93  thf('56', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.93         (~ (v1_xboole_0 @ X2)
% 0.74/0.93          | ((X0) = (k3_xboole_0 @ X1 @ X2))
% 0.74/0.93          | ~ (v1_xboole_0 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['54', '55'])).
% 0.74/0.93  thf('57', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         (((X0) = (k1_xboole_0))
% 0.74/0.93          | ~ (v1_xboole_0 @ X0)
% 0.74/0.93          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.74/0.93      inference('sup+', [status(thm)], ['51', '56'])).
% 0.74/0.93  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.74/0.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.74/0.93  thf('59', plain,
% 0.74/0.93      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.93      inference('demod', [status(thm)], ['57', '58'])).
% 0.74/0.93  thf('60', plain,
% 0.74/0.93      ((((k3_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.74/0.93         <= ((![X12 : $i]:
% 0.74/0.93                (~ (r2_hidden @ X12 @ sk_A) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['40', '59'])).
% 0.74/0.93  thf('61', plain,
% 0.74/0.93      (![X9 : $i, X11 : $i]:
% 0.74/0.93         ((r1_xboole_0 @ X9 @ X11)
% 0.74/0.93          | ((k3_xboole_0 @ X9 @ X11) != (k1_xboole_0)))),
% 0.74/0.93      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.74/0.93  thf('62', plain,
% 0.74/0.93      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B_1)))
% 0.74/0.93         <= ((![X12 : $i]:
% 0.74/0.93                (~ (r2_hidden @ X12 @ sk_A) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['60', '61'])).
% 0.74/0.93  thf('63', plain,
% 0.74/0.93      (((r1_xboole_0 @ sk_A @ sk_B_1))
% 0.74/0.93         <= ((![X12 : $i]:
% 0.74/0.93                (~ (r2_hidden @ X12 @ sk_A) | ~ (r2_hidden @ X12 @ sk_B_1))))),
% 0.74/0.93      inference('simplify', [status(thm)], ['62'])).
% 0.74/0.93  thf('64', plain,
% 0.74/0.93      ((~ (r1_xboole_0 @ sk_A @ sk_B_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B_1)))),
% 0.74/0.93      inference('split', [status(esa)], ['8'])).
% 0.74/0.93  thf('65', plain,
% 0.74/0.93      (((r1_xboole_0 @ sk_A @ sk_B_1)) | 
% 0.74/0.93       ~
% 0.74/0.93       (![X12 : $i]:
% 0.74/0.93          (~ (r2_hidden @ X12 @ sk_A) | ~ (r2_hidden @ X12 @ sk_B_1)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['63', '64'])).
% 0.74/0.93  thf('66', plain, ($false),
% 0.74/0.93      inference('sat_resolution*', [status(thm)],
% 0.74/0.93                ['1', '3', '5', '12', '13', '27', '28', '65'])).
% 0.74/0.93  
% 0.74/0.93  % SZS output end Refutation
% 0.74/0.93  
% 0.79/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
