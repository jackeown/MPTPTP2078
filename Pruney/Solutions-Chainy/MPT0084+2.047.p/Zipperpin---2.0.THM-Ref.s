%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.85ZqlD2GJs

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 136 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :   21
%              Number of atoms          :  557 ( 943 expanded)
%              Number of equality atoms :   41 (  59 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('2',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('4',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('6',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('12',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
    | ( r1_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('13',plain,(
    ! [X19: $i] :
      ( r1_xboole_0 @ X19 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('18',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('20',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('29',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
    = ( k3_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X19: $i] :
      ( r1_xboole_0 @ X19 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('38',plain,
    ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) )
    | ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('40',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('42',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('44',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('48',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('55',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('57',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['46','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('64',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    r1_xboole_0 @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['1','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.85ZqlD2GJs
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 120 iterations in 0.053s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(t77_xboole_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.52          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.52        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.52             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 0.21/0.52  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t4_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X2 @ X3)
% 0.21/0.52          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.52  thf('2', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.52  thf('4', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf(t7_xboole_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.21/0.52          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.52  thf(t16_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.52       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.52         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 0.21/0.52           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (((k3_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A)) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf(t75_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.52          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X20 @ X21)
% 0.21/0.52          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      ((~ (r1_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A))
% 0.21/0.52        | (r1_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.52  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.52  thf('13', plain, (![X19 : $i]: (r1_xboole_0 @ X19 @ k1_xboole_0)),
% 0.21/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.52  thf('15', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain, ((r1_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['12', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.52  thf('18', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_B_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (((k3_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.52         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 0.21/0.52           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (((k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('23', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(l32_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X7 : $i, X9 : $i]:
% 0.21/0.52         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.52  thf('25', plain, (((k4_xboole_0 @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf(t48_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.52           = (k3_xboole_0 @ X14 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf(t3_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.52  thf('28', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.52  thf('29', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.52         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 0.21/0.52           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k3_xboole_0 @ sk_A @ X0)
% 0.21/0.52           = (k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B_1))
% 0.21/0.52         = (k3_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['22', '31'])).
% 0.21/0.52  thf('33', plain, (![X19 : $i]: (r1_xboole_0 @ X19 @ k1_xboole_0)),
% 0.21/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['32', '35'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X20 @ X21)
% 0.21/0.52          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      ((~ (r1_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1))
% 0.21/0.52        | (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('39', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('40', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.52  thf('42', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1) @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B_1) @ sk_A) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.52         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 0.21/0.52           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_A)) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.52  thf('47', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.52           = (k3_xboole_0 @ X14 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['47', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.21/0.52           = (k3_xboole_0 @ X14 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['51', '52'])).
% 0.21/0.52  thf('54', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.52  thf('55', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.52         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 0.21/0.52           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.21/0.52          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.21/0.52          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.52          | ~ (r1_xboole_0 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['55', '58'])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.52         ((k3_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ X12)
% 0.21/0.52           = (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.21/0.52  thf('61', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.52          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r1_xboole_0 @ k1_xboole_0 @ sk_B_1)
% 0.21/0.52          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_A @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['46', '61'])).
% 0.21/0.52  thf('63', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.52  thf('65', plain, ((r1_xboole_0 @ sk_A @ sk_B_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '64'])).
% 0.21/0.52  thf('66', plain, ($false), inference('demod', [status(thm)], ['0', '65'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
