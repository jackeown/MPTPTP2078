%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oigJsG7ioU

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:40 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 143 expanded)
%              Number of leaves         :   20 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  599 (1036 expanded)
%              Number of equality atoms :   53 ( 100 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t83_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_xboole_0 @ A @ B )
      <=> ( ( k4_xboole_0 @ A @ B )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t83_xboole_1])).

thf('0',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X29 @ X30 ) @ X30 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('6',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('8',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['3','8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['23'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('26',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','35'])).

thf('37',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('38',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X28 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ X16 )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('43',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('45',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('51',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('54',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X29 @ X30 ) @ X30 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','58'])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['36','59'])).

thf('61',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('64',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('66',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['3','8'])).

thf('67',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oigJsG7ioU
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:14:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.83/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.00  % Solved by: fo/fo7.sh
% 0.83/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.00  % done 1007 iterations in 0.528s
% 0.83/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.00  % SZS output start Refutation
% 0.83/1.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.83/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.00  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.83/1.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.83/1.00  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.83/1.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.83/1.00  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.83/1.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.83/1.00  thf(t83_xboole_1, conjecture,
% 0.83/1.00    (![A:$i,B:$i]:
% 0.83/1.00     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.83/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.00    (~( ![A:$i,B:$i]:
% 0.83/1.00        ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ) )),
% 0.83/1.00    inference('cnf.neg', [status(esa)], [t83_xboole_1])).
% 0.83/1.00  thf('0', plain,
% 0.83/1.00      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('1', plain,
% 0.83/1.00      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.83/1.00      inference('split', [status(esa)], ['0'])).
% 0.83/1.00  thf('2', plain,
% 0.83/1.00      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)) | ~ (r1_xboole_0 @ sk_A @ sk_B))),
% 0.83/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.00  thf('3', plain,
% 0.83/1.00      (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))) | 
% 0.83/1.00       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 0.83/1.00      inference('split', [status(esa)], ['2'])).
% 0.83/1.00  thf('4', plain,
% 0.83/1.00      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 0.83/1.00         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.83/1.00      inference('split', [status(esa)], ['0'])).
% 0.83/1.00  thf(t79_xboole_1, axiom,
% 0.83/1.00    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.83/1.00  thf('5', plain,
% 0.83/1.00      (![X29 : $i, X30 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X29 @ X30) @ X30)),
% 0.83/1.00      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.83/1.00  thf('6', plain,
% 0.83/1.00      (((r1_xboole_0 @ sk_A @ sk_B))
% 0.83/1.00         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.83/1.00      inference('sup+', [status(thm)], ['4', '5'])).
% 0.83/1.00  thf('7', plain,
% 0.83/1.00      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 0.83/1.00      inference('split', [status(esa)], ['2'])).
% 0.83/1.00  thf('8', plain,
% 0.83/1.00      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 0.83/1.00       ~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.83/1.00      inference('sup-', [status(thm)], ['6', '7'])).
% 0.83/1.00  thf('9', plain,
% 0.83/1.00      (((r1_xboole_0 @ sk_A @ sk_B)) | (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.83/1.00      inference('split', [status(esa)], ['0'])).
% 0.83/1.00  thf('10', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 0.83/1.00      inference('sat_resolution*', [status(thm)], ['3', '8', '9'])).
% 0.83/1.00  thf('11', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.83/1.00      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 0.83/1.00  thf(t4_xboole_0, axiom,
% 0.83/1.00    (![A:$i,B:$i]:
% 0.83/1.00     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.83/1.00            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.83/1.00       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.83/1.00            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.83/1.00  thf('12', plain,
% 0.83/1.00      (![X8 : $i, X9 : $i]:
% 0.83/1.00         ((r1_xboole_0 @ X8 @ X9)
% 0.83/1.00          | (r2_hidden @ (sk_C @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 0.83/1.00      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.83/1.00  thf(t48_xboole_1, axiom,
% 0.83/1.00    (![A:$i,B:$i]:
% 0.83/1.00     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.83/1.00  thf('13', plain,
% 0.83/1.00      (![X22 : $i, X23 : $i]:
% 0.83/1.00         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.83/1.00           = (k3_xboole_0 @ X22 @ X23))),
% 0.83/1.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.83/1.00  thf(d5_xboole_0, axiom,
% 0.83/1.00    (![A:$i,B:$i,C:$i]:
% 0.83/1.00     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.83/1.00       ( ![D:$i]:
% 0.83/1.00         ( ( r2_hidden @ D @ C ) <=>
% 0.83/1.00           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.83/1.00  thf('14', plain,
% 0.83/1.00      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.83/1.00         (~ (r2_hidden @ X4 @ X3)
% 0.83/1.00          | (r2_hidden @ X4 @ X1)
% 0.83/1.00          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.83/1.00      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.83/1.00  thf('15', plain,
% 0.83/1.00      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.83/1.00         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.83/1.00      inference('simplify', [status(thm)], ['14'])).
% 0.83/1.00  thf('16', plain,
% 0.83/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.00         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.83/1.00      inference('sup-', [status(thm)], ['13', '15'])).
% 0.83/1.00  thf('17', plain,
% 0.83/1.00      (![X0 : $i, X1 : $i]:
% 0.83/1.00         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.83/1.00      inference('sup-', [status(thm)], ['12', '16'])).
% 0.83/1.00  thf('18', plain,
% 0.83/1.00      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.83/1.00         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.83/1.00          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.83/1.00      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.83/1.00  thf('19', plain,
% 0.83/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.00         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.83/1.00          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.83/1.00      inference('sup-', [status(thm)], ['17', '18'])).
% 0.83/1.00  thf('20', plain,
% 0.83/1.00      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.83/1.00      inference('sup-', [status(thm)], ['11', '19'])).
% 0.83/1.00  thf(symmetry_r1_xboole_0, axiom,
% 0.83/1.00    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.83/1.00  thf('21', plain,
% 0.83/1.00      (![X6 : $i, X7 : $i]:
% 0.83/1.00         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.83/1.00      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.83/1.00  thf('22', plain,
% 0.83/1.00      (![X0 : $i]: (r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.83/1.00      inference('sup-', [status(thm)], ['20', '21'])).
% 0.83/1.00  thf('23', plain,
% 0.83/1.00      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.83/1.00         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.83/1.00          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.83/1.00          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.83/1.00      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.83/1.00  thf('24', plain,
% 0.83/1.00      (![X0 : $i, X1 : $i]:
% 0.83/1.00         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.83/1.00          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.83/1.00      inference('eq_fact', [status(thm)], ['23'])).
% 0.83/1.00  thf(t3_boole, axiom,
% 0.83/1.00    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.83/1.00  thf('25', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.83/1.00      inference('cnf', [status(esa)], [t3_boole])).
% 0.83/1.00  thf('26', plain,
% 0.83/1.00      (![X22 : $i, X23 : $i]:
% 0.83/1.00         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.83/1.00           = (k3_xboole_0 @ X22 @ X23))),
% 0.83/1.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.83/1.00  thf('27', plain,
% 0.83/1.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.83/1.00      inference('sup+', [status(thm)], ['25', '26'])).
% 0.83/1.00  thf(t47_xboole_1, axiom,
% 0.83/1.00    (![A:$i,B:$i]:
% 0.83/1.00     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.83/1.00  thf('28', plain,
% 0.83/1.00      (![X20 : $i, X21 : $i]:
% 0.83/1.00         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 0.83/1.00           = (k4_xboole_0 @ X20 @ X21))),
% 0.83/1.00      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.83/1.00  thf('29', plain,
% 0.83/1.00      (![X0 : $i]:
% 0.83/1.00         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 0.83/1.00           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.83/1.00      inference('sup+', [status(thm)], ['27', '28'])).
% 0.83/1.00  thf('30', plain,
% 0.83/1.00      (![X22 : $i, X23 : $i]:
% 0.83/1.00         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 0.83/1.00           = (k3_xboole_0 @ X22 @ X23))),
% 0.83/1.00      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.83/1.00  thf('31', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.83/1.00      inference('cnf', [status(esa)], [t3_boole])).
% 0.83/1.00  thf('32', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.83/1.00      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.83/1.00  thf('33', plain,
% 0.83/1.00      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.83/1.00         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.83/1.00          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.83/1.00      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.83/1.00  thf('34', plain,
% 0.83/1.00      (![X0 : $i, X1 : $i]:
% 0.83/1.00         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.83/1.00      inference('sup-', [status(thm)], ['32', '33'])).
% 0.83/1.00  thf('35', plain,
% 0.83/1.00      (![X0 : $i, X1 : $i]:
% 0.83/1.00         (((X0) = (k4_xboole_0 @ X0 @ X1)) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.83/1.00      inference('sup-', [status(thm)], ['24', '34'])).
% 0.83/1.00  thf('36', plain,
% 0.83/1.00      (![X0 : $i]:
% 0.83/1.00         ((k3_xboole_0 @ sk_A @ sk_B)
% 0.83/1.00           = (k4_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0))),
% 0.83/1.00      inference('sup-', [status(thm)], ['22', '35'])).
% 0.83/1.00  thf('37', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.83/1.00      inference('cnf', [status(esa)], [t3_boole])).
% 0.83/1.00  thf(t51_xboole_1, axiom,
% 0.83/1.00    (![A:$i,B:$i]:
% 0.83/1.00     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.83/1.00       ( A ) ))).
% 0.83/1.00  thf('38', plain,
% 0.83/1.00      (![X27 : $i, X28 : $i]:
% 0.83/1.00         ((k2_xboole_0 @ (k3_xboole_0 @ X27 @ X28) @ (k4_xboole_0 @ X27 @ X28))
% 0.83/1.00           = (X27))),
% 0.83/1.00      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.83/1.00  thf('39', plain,
% 0.83/1.00      (![X0 : $i]:
% 0.83/1.00         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (X0))),
% 0.83/1.00      inference('sup+', [status(thm)], ['37', '38'])).
% 0.83/1.00  thf(t40_xboole_1, axiom,
% 0.83/1.00    (![A:$i,B:$i]:
% 0.83/1.00     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.83/1.00  thf('40', plain,
% 0.83/1.00      (![X15 : $i, X16 : $i]:
% 0.83/1.00         ((k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ X16)
% 0.83/1.00           = (k4_xboole_0 @ X15 @ X16))),
% 0.83/1.00      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.83/1.00  thf('41', plain,
% 0.83/1.00      (![X0 : $i]:
% 0.83/1.00         ((k4_xboole_0 @ X0 @ X0)
% 0.83/1.00           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 0.83/1.00      inference('sup+', [status(thm)], ['39', '40'])).
% 0.83/1.00  thf('42', plain,
% 0.83/1.00      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.83/1.00         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.83/1.00          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.83/1.00          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.83/1.00      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.83/1.00  thf('43', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.83/1.00      inference('cnf', [status(esa)], [t3_boole])).
% 0.83/1.00  thf('44', plain,
% 0.83/1.00      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.83/1.00         (~ (r2_hidden @ X4 @ X3)
% 0.83/1.00          | ~ (r2_hidden @ X4 @ X2)
% 0.83/1.00          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.83/1.00      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.83/1.00  thf('45', plain,
% 0.83/1.00      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.83/1.00         (~ (r2_hidden @ X4 @ X2)
% 0.83/1.00          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.83/1.00      inference('simplify', [status(thm)], ['44'])).
% 0.83/1.00  thf('46', plain,
% 0.83/1.00      (![X0 : $i, X1 : $i]:
% 0.83/1.00         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.83/1.00      inference('sup-', [status(thm)], ['43', '45'])).
% 0.83/1.00  thf('47', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.83/1.00      inference('condensation', [status(thm)], ['46'])).
% 0.83/1.00  thf('48', plain,
% 0.83/1.00      (![X0 : $i, X1 : $i]:
% 0.83/1.00         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.83/1.00          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.83/1.00      inference('sup-', [status(thm)], ['42', '47'])).
% 0.83/1.00  thf('49', plain,
% 0.83/1.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.83/1.00      inference('sup+', [status(thm)], ['25', '26'])).
% 0.83/1.00  thf('50', plain,
% 0.83/1.00      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.83/1.00      inference('sup+', [status(thm)], ['25', '26'])).
% 0.83/1.00  thf('51', plain,
% 0.83/1.00      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.83/1.00         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.83/1.00          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.83/1.00      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.83/1.00  thf('52', plain,
% 0.83/1.00      (![X0 : $i, X1 : $i]:
% 0.83/1.00         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.83/1.00          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.83/1.00      inference('sup-', [status(thm)], ['50', '51'])).
% 0.83/1.00  thf('53', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.83/1.00      inference('cnf', [status(esa)], [t3_boole])).
% 0.83/1.00  thf('54', plain,
% 0.83/1.00      (![X29 : $i, X30 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X29 @ X30) @ X30)),
% 0.83/1.00      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.83/1.00  thf('55', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.83/1.00      inference('sup+', [status(thm)], ['53', '54'])).
% 0.83/1.00  thf('56', plain,
% 0.83/1.00      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.83/1.00      inference('demod', [status(thm)], ['52', '55'])).
% 0.83/1.00  thf('57', plain,
% 0.83/1.00      (![X0 : $i, X1 : $i]:
% 0.83/1.00         ~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.83/1.00      inference('sup-', [status(thm)], ['49', '56'])).
% 0.83/1.00  thf('58', plain,
% 0.83/1.00      (![X0 : $i, X1 : $i]:
% 0.83/1.00         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1))),
% 0.83/1.00      inference('sup-', [status(thm)], ['48', '57'])).
% 0.83/1.00  thf('59', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.83/1.00      inference('demod', [status(thm)], ['41', '58'])).
% 0.83/1.00  thf('60', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.83/1.00      inference('sup+', [status(thm)], ['36', '59'])).
% 0.83/1.00  thf('61', plain,
% 0.83/1.00      (![X20 : $i, X21 : $i]:
% 0.83/1.00         ((k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21))
% 0.83/1.00           = (k4_xboole_0 @ X20 @ X21))),
% 0.83/1.00      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.83/1.00  thf('62', plain,
% 0.83/1.00      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.83/1.00      inference('sup+', [status(thm)], ['60', '61'])).
% 0.83/1.00  thf('63', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.83/1.00      inference('cnf', [status(esa)], [t3_boole])).
% 0.83/1.00  thf('64', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.83/1.00      inference('demod', [status(thm)], ['62', '63'])).
% 0.83/1.00  thf('65', plain,
% 0.83/1.00      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)))
% 0.83/1.00         <= (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 0.83/1.00      inference('split', [status(esa)], ['2'])).
% 0.83/1.00  thf('66', plain, (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 0.83/1.00      inference('sat_resolution*', [status(thm)], ['3', '8'])).
% 0.83/1.00  thf('67', plain, (((k4_xboole_0 @ sk_A @ sk_B) != (sk_A))),
% 0.83/1.00      inference('simpl_trail', [status(thm)], ['65', '66'])).
% 0.83/1.00  thf('68', plain, ($false),
% 0.83/1.00      inference('simplify_reflect-', [status(thm)], ['64', '67'])).
% 0.83/1.00  
% 0.83/1.00  % SZS output end Refutation
% 0.83/1.00  
% 0.83/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
