%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CS2xhJXiAb

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:32 EST 2020

% Result     : Theorem 2.73s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 144 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   19
%              Number of atoms          :  576 (1202 expanded)
%              Number of equality atoms :   25 (  43 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k4_xboole_0 @ X36 @ ( k1_tarski @ X37 ) )
        = X36 )
      | ( r2_hidden @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) )
      | ( r2_hidden @ sk_D @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','22'])).

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

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('26',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_2 )
    = sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ sk_B ) )
      | ~ ( r1_xboole_0 @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k4_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_B ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['24','33'])).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','46'])).

thf('48',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r2_hidden @ sk_D @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','52'])).

thf('54',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','53'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('55',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','56'])).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('59',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CS2xhJXiAb
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:26:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.73/2.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.73/2.91  % Solved by: fo/fo7.sh
% 2.73/2.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.73/2.91  % done 4183 iterations in 2.493s
% 2.73/2.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.73/2.91  % SZS output start Refutation
% 2.73/2.91  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.73/2.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.73/2.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.73/2.91  thf(sk_D_type, type, sk_D: $i).
% 2.73/2.91  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.73/2.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.73/2.91  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.73/2.91  thf(sk_A_type, type, sk_A: $i).
% 2.73/2.91  thf(sk_B_type, type, sk_B: $i).
% 2.73/2.91  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.73/2.91  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.73/2.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.73/2.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.73/2.91  thf(t149_zfmisc_1, conjecture,
% 2.73/2.91    (![A:$i,B:$i,C:$i,D:$i]:
% 2.73/2.91     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.73/2.91         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.73/2.91       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.73/2.91  thf(zf_stmt_0, negated_conjecture,
% 2.73/2.91    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.73/2.91        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.73/2.91            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.73/2.91          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 2.73/2.91    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 2.73/2.91  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('1', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf(symmetry_r1_xboole_0, axiom,
% 2.73/2.91    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.73/2.91  thf('2', plain,
% 2.73/2.91      (![X2 : $i, X3 : $i]:
% 2.73/2.91         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.73/2.91      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.73/2.91  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 2.73/2.91      inference('sup-', [status(thm)], ['1', '2'])).
% 2.73/2.91  thf(t4_xboole_0, axiom,
% 2.73/2.91    (![A:$i,B:$i]:
% 2.73/2.91     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.73/2.91            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.73/2.91       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.73/2.91            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.73/2.91  thf('4', plain,
% 2.73/2.91      (![X8 : $i, X9 : $i]:
% 2.73/2.91         ((r1_xboole_0 @ X8 @ X9)
% 2.73/2.91          | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 2.73/2.91      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.73/2.91  thf(t65_zfmisc_1, axiom,
% 2.73/2.91    (![A:$i,B:$i]:
% 2.73/2.91     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.73/2.91       ( ~( r2_hidden @ B @ A ) ) ))).
% 2.73/2.91  thf('5', plain,
% 2.73/2.91      (![X36 : $i, X37 : $i]:
% 2.73/2.91         (((k4_xboole_0 @ X36 @ (k1_tarski @ X37)) = (X36))
% 2.73/2.91          | (r2_hidden @ X37 @ X36))),
% 2.73/2.91      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.73/2.91  thf(t48_xboole_1, axiom,
% 2.73/2.91    (![A:$i,B:$i]:
% 2.73/2.91     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.73/2.91  thf('6', plain,
% 2.73/2.91      (![X17 : $i, X18 : $i]:
% 2.73/2.91         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 2.73/2.91           = (k3_xboole_0 @ X17 @ X18))),
% 2.73/2.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.73/2.91  thf('7', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i]:
% 2.73/2.91         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 2.73/2.91          | (r2_hidden @ X1 @ X0))),
% 2.73/2.91      inference('sup+', [status(thm)], ['5', '6'])).
% 2.73/2.91  thf('8', plain,
% 2.73/2.91      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf(commutativity_k3_xboole_0, axiom,
% 2.73/2.91    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.73/2.91  thf('9', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.73/2.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.73/2.91  thf('10', plain,
% 2.73/2.91      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 2.73/2.91      inference('demod', [status(thm)], ['8', '9'])).
% 2.73/2.91  thf(t28_xboole_1, axiom,
% 2.73/2.91    (![A:$i,B:$i]:
% 2.73/2.91     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.73/2.91  thf('11', plain,
% 2.73/2.91      (![X15 : $i, X16 : $i]:
% 2.73/2.91         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 2.73/2.91      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.73/2.91  thf('12', plain,
% 2.73/2.91      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 2.73/2.91         = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.73/2.91      inference('sup-', [status(thm)], ['10', '11'])).
% 2.73/2.91  thf('13', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.73/2.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.73/2.91  thf('14', plain,
% 2.73/2.91      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 2.73/2.91         = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.73/2.91      inference('demod', [status(thm)], ['12', '13'])).
% 2.73/2.91  thf(t16_xboole_1, axiom,
% 2.73/2.91    (![A:$i,B:$i,C:$i]:
% 2.73/2.91     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 2.73/2.91       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.73/2.91  thf('15', plain,
% 2.73/2.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.73/2.91         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 2.73/2.91           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 2.73/2.91      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.73/2.91  thf('16', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.73/2.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.73/2.91  thf('17', plain,
% 2.73/2.91      (![X8 : $i, X10 : $i, X11 : $i]:
% 2.73/2.91         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 2.73/2.91          | ~ (r1_xboole_0 @ X8 @ X11))),
% 2.73/2.91      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.73/2.91  thf('18', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.91         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.73/2.91          | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.73/2.91      inference('sup-', [status(thm)], ['16', '17'])).
% 2.73/2.91  thf('19', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.73/2.91         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 2.73/2.91          | ~ (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 2.73/2.91      inference('sup-', [status(thm)], ['15', '18'])).
% 2.73/2.91  thf('20', plain,
% 2.73/2.91      (![X0 : $i]:
% 2.73/2.91         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 2.73/2.91          | ~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)))),
% 2.73/2.91      inference('sup-', [status(thm)], ['14', '19'])).
% 2.73/2.91  thf('21', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.73/2.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.73/2.91  thf('22', plain,
% 2.73/2.91      (![X0 : $i]:
% 2.73/2.91         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 2.73/2.91          | ~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D))))),
% 2.73/2.91      inference('demod', [status(thm)], ['20', '21'])).
% 2.73/2.91  thf('23', plain,
% 2.73/2.91      (![X0 : $i]:
% 2.73/2.91         (~ (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))
% 2.73/2.91          | (r2_hidden @ sk_D @ sk_B)
% 2.73/2.91          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 2.73/2.91      inference('sup-', [status(thm)], ['7', '22'])).
% 2.73/2.91  thf(t3_xboole_0, axiom,
% 2.73/2.91    (![A:$i,B:$i]:
% 2.73/2.91     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.73/2.91            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.73/2.91       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.73/2.91            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.73/2.91  thf('24', plain,
% 2.73/2.91      (![X4 : $i, X5 : $i]:
% 2.73/2.91         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 2.73/2.91      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.73/2.91  thf('25', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 2.73/2.91      inference('sup-', [status(thm)], ['1', '2'])).
% 2.73/2.91  thf(t83_xboole_1, axiom,
% 2.73/2.91    (![A:$i,B:$i]:
% 2.73/2.91     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.73/2.91  thf('26', plain,
% 2.73/2.91      (![X26 : $i, X27 : $i]:
% 2.73/2.91         (((k4_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_xboole_0 @ X26 @ X27))),
% 2.73/2.91      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.73/2.91  thf('27', plain, (((k4_xboole_0 @ sk_B @ sk_C_2) = (sk_B))),
% 2.73/2.91      inference('sup-', [status(thm)], ['25', '26'])).
% 2.73/2.91  thf('28', plain,
% 2.73/2.91      (![X17 : $i, X18 : $i]:
% 2.73/2.91         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 2.73/2.91           = (k3_xboole_0 @ X17 @ X18))),
% 2.73/2.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.73/2.91  thf('29', plain,
% 2.73/2.91      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C_2))),
% 2.73/2.91      inference('sup+', [status(thm)], ['27', '28'])).
% 2.73/2.91  thf('30', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.91         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.73/2.91          | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.73/2.91      inference('sup-', [status(thm)], ['16', '17'])).
% 2.73/2.91  thf('31', plain,
% 2.73/2.91      (![X0 : $i]:
% 2.73/2.91         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ sk_B))
% 2.73/2.91          | ~ (r1_xboole_0 @ sk_C_2 @ sk_B))),
% 2.73/2.91      inference('sup-', [status(thm)], ['29', '30'])).
% 2.73/2.91  thf('32', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('33', plain,
% 2.73/2.91      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ sk_B))),
% 2.73/2.91      inference('demod', [status(thm)], ['31', '32'])).
% 2.73/2.91  thf('34', plain,
% 2.73/2.91      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B) @ X0)),
% 2.73/2.91      inference('sup-', [status(thm)], ['24', '33'])).
% 2.73/2.91  thf('35', plain,
% 2.73/2.91      (![X2 : $i, X3 : $i]:
% 2.73/2.91         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.73/2.91      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.73/2.91  thf('36', plain,
% 2.73/2.91      (![X0 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_B))),
% 2.73/2.91      inference('sup-', [status(thm)], ['34', '35'])).
% 2.73/2.91  thf('37', plain,
% 2.73/2.91      (![X26 : $i, X27 : $i]:
% 2.73/2.91         (((k4_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_xboole_0 @ X26 @ X27))),
% 2.73/2.91      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.73/2.91  thf('38', plain,
% 2.73/2.91      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_B)) = (X0))),
% 2.73/2.91      inference('sup-', [status(thm)], ['36', '37'])).
% 2.73/2.91  thf('39', plain,
% 2.73/2.91      (![X17 : $i, X18 : $i]:
% 2.73/2.91         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 2.73/2.91           = (k3_xboole_0 @ X17 @ X18))),
% 2.73/2.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.73/2.91  thf('40', plain,
% 2.73/2.91      (![X0 : $i]:
% 2.73/2.91         ((k4_xboole_0 @ X0 @ X0)
% 2.73/2.91           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_B)))),
% 2.73/2.91      inference('sup+', [status(thm)], ['38', '39'])).
% 2.73/2.91  thf('41', plain,
% 2.73/2.91      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B) @ X0)),
% 2.73/2.91      inference('sup-', [status(thm)], ['24', '33'])).
% 2.73/2.91  thf('42', plain,
% 2.73/2.91      (![X4 : $i, X5 : $i]:
% 2.73/2.91         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X5))),
% 2.73/2.91      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.73/2.91  thf('43', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.91         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.73/2.91          | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.73/2.91      inference('sup-', [status(thm)], ['16', '17'])).
% 2.73/2.91  thf('44', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.91         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.73/2.91          | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.73/2.91      inference('sup-', [status(thm)], ['42', '43'])).
% 2.73/2.91  thf('45', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i]:
% 2.73/2.91         (r1_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_B)))),
% 2.73/2.91      inference('sup-', [status(thm)], ['41', '44'])).
% 2.73/2.91  thf('46', plain,
% 2.73/2.91      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 2.73/2.91      inference('sup+', [status(thm)], ['40', '45'])).
% 2.73/2.91  thf('47', plain,
% 2.73/2.91      (![X0 : $i]:
% 2.73/2.91         ((r2_hidden @ sk_D @ sk_B)
% 2.73/2.91          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 2.73/2.91      inference('demod', [status(thm)], ['23', '46'])).
% 2.73/2.91  thf('48', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('49', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 2.73/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.91  thf('50', plain,
% 2.73/2.91      (![X4 : $i, X6 : $i, X7 : $i]:
% 2.73/2.91         (~ (r2_hidden @ X6 @ X4)
% 2.73/2.91          | ~ (r2_hidden @ X6 @ X7)
% 2.73/2.91          | ~ (r1_xboole_0 @ X4 @ X7))),
% 2.73/2.91      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.73/2.91  thf('51', plain,
% 2.73/2.91      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 2.73/2.91      inference('sup-', [status(thm)], ['49', '50'])).
% 2.73/2.91  thf('52', plain, (~ (r2_hidden @ sk_D @ sk_B)),
% 2.73/2.91      inference('sup-', [status(thm)], ['48', '51'])).
% 2.73/2.91  thf('53', plain,
% 2.73/2.91      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))),
% 2.73/2.91      inference('clc', [status(thm)], ['47', '52'])).
% 2.73/2.91  thf('54', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 2.73/2.91      inference('sup-', [status(thm)], ['4', '53'])).
% 2.73/2.91  thf(t70_xboole_1, axiom,
% 2.73/2.91    (![A:$i,B:$i,C:$i]:
% 2.73/2.91     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.73/2.91            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.73/2.91       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.73/2.91            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 2.73/2.91  thf('55', plain,
% 2.73/2.91      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.73/2.91         ((r1_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 2.73/2.91          | ~ (r1_xboole_0 @ X19 @ X20)
% 2.73/2.91          | ~ (r1_xboole_0 @ X19 @ X21))),
% 2.73/2.91      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.73/2.91  thf('56', plain,
% 2.73/2.91      (![X0 : $i]:
% 2.73/2.91         (~ (r1_xboole_0 @ sk_B @ X0)
% 2.73/2.91          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 2.73/2.91      inference('sup-', [status(thm)], ['54', '55'])).
% 2.73/2.91  thf('57', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_2))),
% 2.73/2.91      inference('sup-', [status(thm)], ['3', '56'])).
% 2.73/2.91  thf('58', plain,
% 2.73/2.91      (![X2 : $i, X3 : $i]:
% 2.73/2.91         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.73/2.91      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.73/2.91  thf('59', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 2.73/2.91      inference('sup-', [status(thm)], ['57', '58'])).
% 2.73/2.91  thf('60', plain, ($false), inference('demod', [status(thm)], ['0', '59'])).
% 2.73/2.91  
% 2.73/2.91  % SZS output end Refutation
% 2.73/2.91  
% 2.73/2.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
