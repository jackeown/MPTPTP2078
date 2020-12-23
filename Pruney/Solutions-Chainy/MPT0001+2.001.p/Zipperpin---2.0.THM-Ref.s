%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VfAXyJbxGD

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:42 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 409 expanded)
%              Number of leaves         :   11 ( 102 expanded)
%              Depth                    :   18
%              Number of atoms          :  698 (4361 expanded)
%              Number of equality atoms :   12 (  90 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t1_xboole_0,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
      <=> ~ ( ( r2_hidden @ A @ B )
          <=> ( r2_hidden @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_xboole_0])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('5',plain,
    ( ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
      | ~ ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
   <= ( ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('16',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ( ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('20',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( r2_hidden @ X6 @ X9 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ X0 ) )
        | ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['19','26'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['28'])).

thf('35',plain,
    ( ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_C @ sk_B ) )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('37',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) )
      | ( r2_hidden @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('40',plain,
    ( ( ( r2_hidden @ sk_A @ sk_C )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['31','32','33','34','44'])).

thf('46',plain,(
    ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['29','45'])).

thf('47',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['17','18','49'])).

thf('51',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','50'])).

thf('52',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k5_xboole_0 @ X12 @ X13 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('53',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('54',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['28'])).

thf('57',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('58',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('59',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['31','56','57','17','18','49','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference(simpl_trail,[status(thm)],['55','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k5_xboole_0 @ X0 @ sk_C ) )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','63'])).

thf('65',plain,(
    ~ ( r2_hidden @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['29','45'])).

thf('66',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['51','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VfAXyJbxGD
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:57:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.52/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.76  % Solved by: fo/fo7.sh
% 0.52/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.76  % done 406 iterations in 0.316s
% 0.52/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.76  % SZS output start Refutation
% 0.52/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.76  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.52/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.76  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.76  thf(t1_xboole_0, conjecture,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.52/0.76       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.52/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.76    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.76        ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.52/0.76          ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ) )),
% 0.52/0.76    inference('cnf.neg', [status(esa)], [t1_xboole_0])).
% 0.52/0.76  thf('0', plain,
% 0.52/0.76      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.52/0.76        | ~ (r2_hidden @ sk_A @ sk_C)
% 0.52/0.76        | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('1', plain,
% 0.52/0.76      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.76      inference('split', [status(esa)], ['0'])).
% 0.52/0.76  thf('2', plain,
% 0.52/0.76      (((r2_hidden @ sk_A @ sk_B)
% 0.52/0.76        | (r2_hidden @ sk_A @ sk_C)
% 0.52/0.76        | (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('3', plain,
% 0.52/0.76      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.52/0.76      inference('split', [status(esa)], ['2'])).
% 0.52/0.76  thf('4', plain,
% 0.52/0.76      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.76      inference('split', [status(esa)], ['2'])).
% 0.52/0.76  thf('5', plain,
% 0.52/0.76      (((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 0.52/0.76         <= (((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.52/0.76      inference('split', [status(esa)], ['0'])).
% 0.52/0.76  thf(d6_xboole_0, axiom,
% 0.52/0.76    (![A:$i,B:$i]:
% 0.52/0.76     ( ( k5_xboole_0 @ A @ B ) =
% 0.52/0.76       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.52/0.76  thf('6', plain,
% 0.52/0.76      (![X12 : $i, X13 : $i]:
% 0.52/0.76         ((k5_xboole_0 @ X12 @ X13)
% 0.52/0.76           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 0.52/0.76              (k4_xboole_0 @ X13 @ X12)))),
% 0.52/0.76      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.52/0.76  thf(d3_xboole_0, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.52/0.76       ( ![D:$i]:
% 0.52/0.76         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.76           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.52/0.76  thf('7', plain,
% 0.52/0.76      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X4 @ X2)
% 0.52/0.76          | (r2_hidden @ X4 @ X3)
% 0.52/0.76          | (r2_hidden @ X4 @ X1)
% 0.52/0.76          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.52/0.76      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.52/0.76  thf('8', plain,
% 0.52/0.76      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.52/0.76         ((r2_hidden @ X4 @ X1)
% 0.52/0.76          | (r2_hidden @ X4 @ X3)
% 0.52/0.76          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['7'])).
% 0.52/0.76  thf('9', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X2 @ (k5_xboole_0 @ X1 @ X0))
% 0.52/0.76          | (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.52/0.76          | (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['6', '8'])).
% 0.52/0.76  thf('10', plain,
% 0.52/0.76      ((((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B))
% 0.52/0.76         | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))
% 0.52/0.76         <= (((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['5', '9'])).
% 0.52/0.76  thf(d5_xboole_0, axiom,
% 0.52/0.76    (![A:$i,B:$i,C:$i]:
% 0.52/0.76     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.52/0.76       ( ![D:$i]:
% 0.52/0.76         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.76           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.52/0.76  thf('11', plain,
% 0.52/0.76      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X10 @ X9)
% 0.52/0.76          | ~ (r2_hidden @ X10 @ X8)
% 0.52/0.76          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.52/0.76      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.52/0.76  thf('12', plain,
% 0.52/0.76      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X10 @ X8)
% 0.52/0.76          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['11'])).
% 0.52/0.76  thf('13', plain,
% 0.52/0.76      ((((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.52/0.76         | ~ (r2_hidden @ sk_A @ sk_B)))
% 0.52/0.76         <= (((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['10', '12'])).
% 0.52/0.76  thf('14', plain,
% 0.52/0.76      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)))
% 0.52/0.76         <= (((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) & 
% 0.52/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['4', '13'])).
% 0.52/0.76  thf('15', plain,
% 0.52/0.76      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X10 @ X8)
% 0.52/0.76          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['11'])).
% 0.52/0.76  thf('16', plain,
% 0.52/0.76      ((~ (r2_hidden @ sk_A @ sk_C))
% 0.52/0.76         <= (((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) & 
% 0.52/0.76             ((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.76  thf('17', plain,
% 0.52/0.76      (~ ((r2_hidden @ sk_A @ sk_B)) | ~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.52/0.76       ~ ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['3', '16'])).
% 0.52/0.76  thf('18', plain,
% 0.52/0.76      (~ ((r2_hidden @ sk_A @ sk_B)) | ~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.52/0.76       ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.52/0.76      inference('split', [status(esa)], ['0'])).
% 0.52/0.76  thf('19', plain,
% 0.52/0.76      (![X12 : $i, X13 : $i]:
% 0.52/0.76         ((k5_xboole_0 @ X12 @ X13)
% 0.52/0.76           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 0.52/0.76              (k4_xboole_0 @ X13 @ X12)))),
% 0.52/0.76      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.52/0.76  thf('20', plain,
% 0.52/0.76      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.76      inference('split', [status(esa)], ['2'])).
% 0.52/0.76  thf('21', plain,
% 0.52/0.76      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X6 @ X7)
% 0.52/0.76          | (r2_hidden @ X6 @ X8)
% 0.52/0.76          | (r2_hidden @ X6 @ X9)
% 0.52/0.76          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.52/0.76      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.52/0.76  thf('22', plain,
% 0.52/0.76      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.76         ((r2_hidden @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 0.52/0.76          | (r2_hidden @ X6 @ X8)
% 0.52/0.76          | ~ (r2_hidden @ X6 @ X7))),
% 0.52/0.76      inference('simplify', [status(thm)], ['21'])).
% 0.52/0.76  thf('23', plain,
% 0.52/0.76      ((![X0 : $i]:
% 0.52/0.76          ((r2_hidden @ sk_A @ X0)
% 0.52/0.76           | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))))
% 0.52/0.76         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['20', '22'])).
% 0.52/0.76  thf('24', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X0 @ X3)
% 0.52/0.76          | (r2_hidden @ X0 @ X2)
% 0.52/0.76          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.52/0.76      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.52/0.76  thf('25', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.52/0.76         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.52/0.76      inference('simplify', [status(thm)], ['24'])).
% 0.52/0.76  thf('26', plain,
% 0.52/0.76      ((![X0 : $i, X1 : $i]:
% 0.52/0.76          ((r2_hidden @ sk_A @ X0)
% 0.52/0.76           | (r2_hidden @ sk_A @ (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ X1))))
% 0.52/0.76         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['23', '25'])).
% 0.52/0.76  thf('27', plain,
% 0.52/0.76      ((![X0 : $i]:
% 0.52/0.76          ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ X0))
% 0.52/0.76           | (r2_hidden @ sk_A @ X0)))
% 0.52/0.76         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.76      inference('sup+', [status(thm)], ['19', '26'])).
% 0.52/0.76  thf('28', plain,
% 0.52/0.76      ((~ (r2_hidden @ sk_A @ sk_C)
% 0.52/0.76        | (r2_hidden @ sk_A @ sk_B)
% 0.52/0.76        | ~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('29', plain,
% 0.52/0.76      ((~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 0.52/0.76         <= (~ ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.52/0.76      inference('split', [status(esa)], ['28'])).
% 0.52/0.76  thf('30', plain,
% 0.52/0.76      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.52/0.76        | (r2_hidden @ sk_A @ sk_C)
% 0.52/0.76        | ~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.52/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.76  thf('31', plain,
% 0.52/0.76      (~ ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 0.52/0.76       ((r2_hidden @ sk_A @ sk_C)) | ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.52/0.76      inference('split', [status(esa)], ['30'])).
% 0.52/0.76  thf('32', plain,
% 0.52/0.76      (~ ((r2_hidden @ sk_A @ sk_C)) | ~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.52/0.76       ~ ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['3', '16'])).
% 0.52/0.76  thf('33', plain,
% 0.52/0.76      (~ ((r2_hidden @ sk_A @ sk_C)) | ~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.52/0.76       ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.52/0.76      inference('split', [status(esa)], ['0'])).
% 0.52/0.76  thf('34', plain,
% 0.52/0.76      (((r2_hidden @ sk_A @ sk_B)) | ~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.52/0.76       ~ ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.52/0.76      inference('split', [status(esa)], ['28'])).
% 0.52/0.76  thf('35', plain,
% 0.52/0.76      ((((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_C @ sk_B))
% 0.52/0.76         | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))
% 0.52/0.76         <= (((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['5', '9'])).
% 0.52/0.76  thf('36', plain,
% 0.52/0.76      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X10 @ X9)
% 0.52/0.76          | (r2_hidden @ X10 @ X7)
% 0.52/0.76          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.52/0.76      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.52/0.76  thf('37', plain,
% 0.52/0.76      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.52/0.76         ((r2_hidden @ X10 @ X7)
% 0.52/0.76          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['36'])).
% 0.52/0.76  thf('38', plain,
% 0.52/0.76      ((((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))
% 0.52/0.76         | (r2_hidden @ sk_A @ sk_C)))
% 0.52/0.76         <= (((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['35', '37'])).
% 0.52/0.76  thf('39', plain,
% 0.52/0.76      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.52/0.76         ((r2_hidden @ X10 @ X7)
% 0.52/0.76          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.52/0.76      inference('simplify', [status(thm)], ['36'])).
% 0.52/0.76  thf('40', plain,
% 0.52/0.76      ((((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_A @ sk_B)))
% 0.52/0.76         <= (((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['38', '39'])).
% 0.52/0.76  thf('41', plain,
% 0.52/0.76      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.52/0.76      inference('split', [status(esa)], ['0'])).
% 0.52/0.76  thf('42', plain,
% 0.52/0.76      (((r2_hidden @ sk_A @ sk_B))
% 0.52/0.76         <= (~ ((r2_hidden @ sk_A @ sk_C)) & 
% 0.52/0.76             ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['40', '41'])).
% 0.52/0.76  thf('43', plain,
% 0.52/0.76      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.76      inference('split', [status(esa)], ['0'])).
% 0.52/0.76  thf('44', plain,
% 0.52/0.76      (((r2_hidden @ sk_A @ sk_B)) | ((r2_hidden @ sk_A @ sk_C)) | 
% 0.52/0.76       ~ ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['42', '43'])).
% 0.52/0.76  thf('45', plain, (~ ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.52/0.76      inference('sat_resolution*', [status(thm)],
% 0.52/0.76                ['31', '32', '33', '34', '44'])).
% 0.52/0.76  thf('46', plain, (~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))),
% 0.52/0.76      inference('simpl_trail', [status(thm)], ['29', '45'])).
% 0.52/0.76  thf('47', plain,
% 0.52/0.76      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['27', '46'])).
% 0.52/0.76  thf('48', plain,
% 0.52/0.76      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.52/0.76      inference('split', [status(esa)], ['0'])).
% 0.52/0.76  thf('49', plain,
% 0.52/0.76      (((r2_hidden @ sk_A @ sk_C)) | ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.52/0.76      inference('sup-', [status(thm)], ['47', '48'])).
% 0.52/0.76  thf('50', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.52/0.76      inference('sat_resolution*', [status(thm)], ['17', '18', '49'])).
% 0.52/0.76  thf('51', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.52/0.76      inference('simpl_trail', [status(thm)], ['1', '50'])).
% 0.52/0.76  thf('52', plain,
% 0.52/0.76      (![X12 : $i, X13 : $i]:
% 0.52/0.76         ((k5_xboole_0 @ X12 @ X13)
% 0.52/0.76           = (k2_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ 
% 0.52/0.76              (k4_xboole_0 @ X13 @ X12)))),
% 0.52/0.76      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.52/0.76  thf('53', plain,
% 0.52/0.76      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.52/0.76      inference('split', [status(esa)], ['2'])).
% 0.52/0.76  thf('54', plain,
% 0.52/0.76      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.52/0.76         ((r2_hidden @ X6 @ (k4_xboole_0 @ X7 @ X8))
% 0.52/0.76          | (r2_hidden @ X6 @ X8)
% 0.52/0.76          | ~ (r2_hidden @ X6 @ X7))),
% 0.52/0.76      inference('simplify', [status(thm)], ['21'])).
% 0.52/0.76  thf('55', plain,
% 0.52/0.76      ((![X0 : $i]:
% 0.52/0.76          ((r2_hidden @ sk_A @ X0)
% 0.52/0.76           | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_C @ X0))))
% 0.52/0.76         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['53', '54'])).
% 0.52/0.76  thf('56', plain,
% 0.52/0.76      (~ ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 0.52/0.76       ~ ((r2_hidden @ sk_A @ sk_C)) | ((r2_hidden @ sk_A @ sk_B))),
% 0.52/0.76      inference('split', [status(esa)], ['28'])).
% 0.52/0.76  thf('57', plain,
% 0.52/0.76      (((r2_hidden @ sk_A @ sk_C)) | ((r2_hidden @ sk_A @ sk_B)) | 
% 0.52/0.76       ~ ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.52/0.76      inference('sup-', [status(thm)], ['42', '43'])).
% 0.52/0.76  thf('58', plain,
% 0.52/0.76      (((r2_hidden @ sk_A @ sk_C)) | ((r2_hidden @ sk_A @ sk_B)) | 
% 0.52/0.76       ((r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 0.52/0.76      inference('split', [status(esa)], ['2'])).
% 0.52/0.76  thf('59', plain, (((r2_hidden @ sk_A @ sk_C))),
% 0.52/0.76      inference('sat_resolution*', [status(thm)],
% 0.52/0.76                ['31', '56', '57', '17', '18', '49', '58'])).
% 0.52/0.76  thf('60', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((r2_hidden @ sk_A @ X0)
% 0.52/0.76          | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_C @ X0)))),
% 0.52/0.76      inference('simpl_trail', [status(thm)], ['55', '59'])).
% 0.52/0.76  thf('61', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.52/0.76         (~ (r2_hidden @ X0 @ X1)
% 0.52/0.76          | (r2_hidden @ X0 @ X2)
% 0.52/0.76          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.52/0.76      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.52/0.76  thf('62', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.52/0.76         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.52/0.76      inference('simplify', [status(thm)], ['61'])).
% 0.52/0.76  thf('63', plain,
% 0.52/0.76      (![X0 : $i, X1 : $i]:
% 0.52/0.76         ((r2_hidden @ sk_A @ X0)
% 0.52/0.76          | (r2_hidden @ sk_A @ (k2_xboole_0 @ X1 @ (k4_xboole_0 @ sk_C @ X0))))),
% 0.52/0.76      inference('sup-', [status(thm)], ['60', '62'])).
% 0.52/0.76  thf('64', plain,
% 0.52/0.76      (![X0 : $i]:
% 0.52/0.76         ((r2_hidden @ sk_A @ (k5_xboole_0 @ X0 @ sk_C))
% 0.52/0.76          | (r2_hidden @ sk_A @ X0))),
% 0.52/0.76      inference('sup+', [status(thm)], ['52', '63'])).
% 0.52/0.76  thf('65', plain, (~ (r2_hidden @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))),
% 0.52/0.76      inference('simpl_trail', [status(thm)], ['29', '45'])).
% 0.52/0.76  thf('66', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.52/0.76      inference('sup-', [status(thm)], ['64', '65'])).
% 0.52/0.76  thf('67', plain, ($false), inference('demod', [status(thm)], ['51', '66'])).
% 0.52/0.76  
% 0.52/0.76  % SZS output end Refutation
% 0.52/0.76  
% 0.52/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
