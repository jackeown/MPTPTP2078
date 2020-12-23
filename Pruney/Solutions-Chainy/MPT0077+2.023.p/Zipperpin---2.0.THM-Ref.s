%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IQ4CjEQaMh

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:24:52 EST 2020

% Result     : Theorem 0.94s
% Output     : Refutation 0.94s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 216 expanded)
%              Number of leaves         :   10 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  593 (2663 expanded)
%              Number of equality atoms :    4 (  14 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t70_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
                & ( r1_xboole_0 @ A @ C ) )
            & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
        & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
            & ( r1_xboole_0 @ A @ B )
            & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_xboole_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ X1 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['15','26','27'])).

thf('29',plain,(
    ~ ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf('30',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_C_1 )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['30'])).

thf('33',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['15','26','27','32'])).

thf('34',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['31','33'])).

thf('35',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['15','26','27','36'])).

thf('38',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('41',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('44',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X1 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_xboole_0 @ sk_A @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_A @ X0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['34','51'])).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    r1_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['29','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IQ4CjEQaMh
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.94/1.14  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.94/1.14  % Solved by: fo/fo7.sh
% 0.94/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.94/1.14  % done 1412 iterations in 0.688s
% 0.94/1.14  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.94/1.14  % SZS output start Refutation
% 0.94/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.94/1.14  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.94/1.14  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.94/1.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.94/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.94/1.14  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.94/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.94/1.14  thf(t70_xboole_1, conjecture,
% 0.94/1.14    (![A:$i,B:$i,C:$i]:
% 0.94/1.14     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.94/1.14            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.94/1.14       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.94/1.14            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.94/1.14  thf(zf_stmt_0, negated_conjecture,
% 0.94/1.14    (~( ![A:$i,B:$i,C:$i]:
% 0.94/1.14        ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.94/1.14               ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.94/1.14          ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.94/1.14               ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ) )),
% 0.94/1.14    inference('cnf.neg', [status(esa)], [t70_xboole_1])).
% 0.94/1.14  thf('0', plain,
% 0.94/1.14      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)
% 0.94/1.14        | ~ (r1_xboole_0 @ sk_A @ sk_B)
% 0.94/1.14        | ~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.94/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.14  thf('1', plain,
% 0.94/1.14      ((~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 0.94/1.14         <= (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.94/1.14      inference('split', [status(esa)], ['0'])).
% 0.94/1.14  thf('2', plain,
% 0.94/1.14      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 0.94/1.14        | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.94/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.14  thf('3', plain,
% 0.94/1.14      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 0.94/1.14         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.94/1.14      inference('split', [status(esa)], ['2'])).
% 0.94/1.14  thf(t3_xboole_0, axiom,
% 0.94/1.14    (![A:$i,B:$i]:
% 0.94/1.14     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.94/1.14            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.94/1.14       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.94/1.14            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.94/1.14  thf('4', plain,
% 0.94/1.14      (![X6 : $i, X7 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.94/1.14      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.94/1.14  thf(d3_xboole_0, axiom,
% 0.94/1.14    (![A:$i,B:$i,C:$i]:
% 0.94/1.14     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.94/1.14       ( ![D:$i]:
% 0.94/1.14         ( ( r2_hidden @ D @ C ) <=>
% 0.94/1.14           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.94/1.14  thf('5', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.94/1.14         (~ (r2_hidden @ X0 @ X3)
% 0.94/1.14          | (r2_hidden @ X0 @ X2)
% 0.94/1.14          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.94/1.14      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.94/1.14  thf('6', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.94/1.14         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.94/1.14      inference('simplify', [status(thm)], ['5'])).
% 0.94/1.14  thf('7', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ X1 @ X0)
% 0.94/1.14          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 0.94/1.14      inference('sup-', [status(thm)], ['4', '6'])).
% 0.94/1.14  thf('8', plain,
% 0.94/1.14      (![X6 : $i, X7 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.94/1.14      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.94/1.14  thf('9', plain,
% 0.94/1.14      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.94/1.14         (~ (r2_hidden @ X8 @ X6)
% 0.94/1.14          | ~ (r2_hidden @ X8 @ X9)
% 0.94/1.14          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.94/1.14      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.94/1.14  thf('10', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ X0 @ X1)
% 0.94/1.14          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.94/1.14          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.94/1.14      inference('sup-', [status(thm)], ['8', '9'])).
% 0.94/1.14  thf('11', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ X2 @ X1)
% 0.94/1.14          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.94/1.14          | (r1_xboole_0 @ X2 @ X1))),
% 0.94/1.14      inference('sup-', [status(thm)], ['7', '10'])).
% 0.94/1.14  thf('12', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.94/1.14         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.94/1.14          | (r1_xboole_0 @ X2 @ X1))),
% 0.94/1.14      inference('simplify', [status(thm)], ['11'])).
% 0.94/1.14  thf('13', plain,
% 0.94/1.14      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.94/1.14         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.94/1.14      inference('sup-', [status(thm)], ['3', '12'])).
% 0.94/1.14  thf('14', plain,
% 0.94/1.14      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.94/1.14      inference('split', [status(esa)], ['0'])).
% 0.94/1.14  thf('15', plain,
% 0.94/1.14      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.94/1.14       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.94/1.14      inference('sup-', [status(thm)], ['13', '14'])).
% 0.94/1.14  thf('16', plain,
% 0.94/1.14      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))
% 0.94/1.14         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.94/1.14      inference('split', [status(esa)], ['2'])).
% 0.94/1.14  thf('17', plain,
% 0.94/1.14      (![X6 : $i, X7 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.94/1.14      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.94/1.14  thf('18', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.94/1.14         (~ (r2_hidden @ X0 @ X1)
% 0.94/1.14          | (r2_hidden @ X0 @ X2)
% 0.94/1.14          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.94/1.14      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.94/1.14  thf('19', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.94/1.14         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.94/1.14      inference('simplify', [status(thm)], ['18'])).
% 0.94/1.14  thf('20', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ X1 @ X0)
% 0.94/1.14          | (r2_hidden @ (sk_C @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.94/1.14      inference('sup-', [status(thm)], ['17', '19'])).
% 0.94/1.14  thf('21', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ X0 @ X1)
% 0.94/1.14          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.94/1.14          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.94/1.14      inference('sup-', [status(thm)], ['8', '9'])).
% 0.94/1.14  thf('22', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ X2 @ X0)
% 0.94/1.14          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.94/1.14          | (r1_xboole_0 @ X2 @ X0))),
% 0.94/1.14      inference('sup-', [status(thm)], ['20', '21'])).
% 0.94/1.14  thf('23', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.94/1.14         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.94/1.14          | (r1_xboole_0 @ X2 @ X0))),
% 0.94/1.14      inference('simplify', [status(thm)], ['22'])).
% 0.94/1.14  thf('24', plain,
% 0.94/1.14      (((r1_xboole_0 @ sk_A @ sk_C_1))
% 0.94/1.14         <= (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))))),
% 0.94/1.14      inference('sup-', [status(thm)], ['16', '23'])).
% 0.94/1.14  thf('25', plain,
% 0.94/1.14      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.94/1.14      inference('split', [status(esa)], ['0'])).
% 0.94/1.14  thf('26', plain,
% 0.94/1.14      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 0.94/1.14       ~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.94/1.14      inference('sup-', [status(thm)], ['24', '25'])).
% 0.94/1.14  thf('27', plain,
% 0.94/1.14      (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))) | 
% 0.94/1.14       ~ ((r1_xboole_0 @ sk_A @ sk_B)) | ~ ((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.94/1.14      inference('split', [status(esa)], ['0'])).
% 0.94/1.14  thf('28', plain, (~ ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.94/1.14      inference('sat_resolution*', [status(thm)], ['15', '26', '27'])).
% 0.94/1.14  thf('29', plain, (~ (r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.94/1.14      inference('simpl_trail', [status(thm)], ['1', '28'])).
% 0.94/1.14  thf('30', plain,
% 0.94/1.14      (((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))
% 0.94/1.14        | (r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.94/1.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.94/1.14  thf('31', plain,
% 0.94/1.14      (((r1_xboole_0 @ sk_A @ sk_C_1)) <= (((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 0.94/1.14      inference('split', [status(esa)], ['30'])).
% 0.94/1.14  thf('32', plain,
% 0.94/1.14      (((r1_xboole_0 @ sk_A @ sk_C_1)) | 
% 0.94/1.14       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.94/1.14      inference('split', [status(esa)], ['30'])).
% 0.94/1.14  thf('33', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 0.94/1.14      inference('sat_resolution*', [status(thm)], ['15', '26', '27', '32'])).
% 0.94/1.14  thf('34', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 0.94/1.14      inference('simpl_trail', [status(thm)], ['31', '33'])).
% 0.94/1.14  thf('35', plain,
% 0.94/1.14      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.94/1.14      inference('split', [status(esa)], ['2'])).
% 0.94/1.14  thf('36', plain,
% 0.94/1.14      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.94/1.14       ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1)))),
% 0.94/1.14      inference('split', [status(esa)], ['2'])).
% 0.94/1.14  thf('37', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.94/1.14      inference('sat_resolution*', [status(thm)], ['15', '26', '27', '36'])).
% 0.94/1.14  thf('38', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.94/1.14      inference('simpl_trail', [status(thm)], ['35', '37'])).
% 0.94/1.14  thf('39', plain,
% 0.94/1.14      (![X6 : $i, X7 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.94/1.14      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.94/1.14  thf('40', plain,
% 0.94/1.14      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.94/1.14         (~ (r2_hidden @ X4 @ X2)
% 0.94/1.14          | (r2_hidden @ X4 @ X3)
% 0.94/1.14          | (r2_hidden @ X4 @ X1)
% 0.94/1.14          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.94/1.14      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.94/1.14  thf('41', plain,
% 0.94/1.14      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.94/1.14         ((r2_hidden @ X4 @ X1)
% 0.94/1.14          | (r2_hidden @ X4 @ X3)
% 0.94/1.14          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.94/1.14      inference('simplify', [status(thm)], ['40'])).
% 0.94/1.14  thf('42', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2)
% 0.94/1.14          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 0.94/1.14          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0))),
% 0.94/1.14      inference('sup-', [status(thm)], ['39', '41'])).
% 0.94/1.14  thf('43', plain,
% 0.94/1.14      (![X6 : $i, X7 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.94/1.14      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.94/1.14  thf('44', plain,
% 0.94/1.14      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.94/1.14         (~ (r2_hidden @ X8 @ X6)
% 0.94/1.14          | ~ (r2_hidden @ X8 @ X9)
% 0.94/1.14          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.94/1.14      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.94/1.14  thf('45', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ X1 @ X0)
% 0.94/1.14          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.94/1.14          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.94/1.14      inference('sup-', [status(thm)], ['43', '44'])).
% 0.94/1.14  thf('46', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.94/1.14         ((r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ X1)
% 0.94/1.14          | (r1_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.94/1.14          | ~ (r1_xboole_0 @ X2 @ X0)
% 0.94/1.14          | (r1_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2))),
% 0.94/1.14      inference('sup-', [status(thm)], ['42', '45'])).
% 0.94/1.14  thf('47', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.94/1.14         (~ (r1_xboole_0 @ X2 @ X0)
% 0.94/1.14          | (r1_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X2)
% 0.94/1.14          | (r2_hidden @ (sk_C @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ X1))),
% 0.94/1.14      inference('simplify', [status(thm)], ['46'])).
% 0.94/1.14  thf('48', plain,
% 0.94/1.14      (![X0 : $i]:
% 0.94/1.14         ((r2_hidden @ (sk_C @ sk_A @ (k2_xboole_0 @ sk_B @ X0)) @ X0)
% 0.94/1.14          | (r1_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.94/1.14      inference('sup-', [status(thm)], ['38', '47'])).
% 0.94/1.14  thf('49', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ X1 @ X0)
% 0.94/1.14          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.94/1.14          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.94/1.14      inference('sup-', [status(thm)], ['43', '44'])).
% 0.94/1.14  thf('50', plain,
% 0.94/1.14      (![X0 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.94/1.14          | ~ (r1_xboole_0 @ sk_A @ X0)
% 0.94/1.14          | (r1_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.94/1.14      inference('sup-', [status(thm)], ['48', '49'])).
% 0.94/1.14  thf('51', plain,
% 0.94/1.14      (![X0 : $i]:
% 0.94/1.14         (~ (r1_xboole_0 @ sk_A @ X0)
% 0.94/1.14          | (r1_xboole_0 @ (k2_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.94/1.14      inference('simplify', [status(thm)], ['50'])).
% 0.94/1.14  thf('52', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 0.94/1.14      inference('sup-', [status(thm)], ['34', '51'])).
% 0.94/1.14  thf('53', plain,
% 0.94/1.14      (![X6 : $i, X7 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.94/1.14      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.94/1.14  thf('54', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ X1 @ X0)
% 0.94/1.14          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.94/1.14          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.94/1.14      inference('sup-', [status(thm)], ['43', '44'])).
% 0.94/1.14  thf('55', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i]:
% 0.94/1.14         ((r1_xboole_0 @ X0 @ X1)
% 0.94/1.14          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.94/1.14          | (r1_xboole_0 @ X0 @ X1))),
% 0.94/1.14      inference('sup-', [status(thm)], ['53', '54'])).
% 0.94/1.14  thf('56', plain,
% 0.94/1.14      (![X0 : $i, X1 : $i]:
% 0.94/1.14         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.94/1.14      inference('simplify', [status(thm)], ['55'])).
% 0.94/1.14  thf('57', plain, ((r1_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.94/1.14      inference('sup-', [status(thm)], ['52', '56'])).
% 0.94/1.14  thf('58', plain, ($false), inference('demod', [status(thm)], ['29', '57'])).
% 0.94/1.14  
% 0.94/1.14  % SZS output end Refutation
% 0.94/1.14  
% 0.98/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
