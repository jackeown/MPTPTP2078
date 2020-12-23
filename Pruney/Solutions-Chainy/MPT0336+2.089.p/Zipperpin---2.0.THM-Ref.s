%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4yZxID85Yz

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:32 EST 2020

% Result     : Theorem 2.99s
% Output     : Refutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 129 expanded)
%              Number of leaves         :   23 (  47 expanded)
%              Depth                    :   22
%              Number of atoms          :  577 (1015 expanded)
%              Number of equality atoms :   34 (  46 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
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
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) )
        = X39 )
      | ( r2_hidden @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X23: $i,X25: $i] :
      ( ( r1_xboole_0 @ X23 @ X25 )
      | ( ( k4_xboole_0 @ X23 @ X25 )
       != X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) )
        = X39 )
      | ( r2_hidden @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_C_1 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('21',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('22',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_C_1 )
    = ( k4_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k4_xboole_0 @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('30',plain,(
    r1_tarski @ sk_C_1 @ sk_C_1 ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X23: $i,X25: $i] :
      ( ( r1_xboole_0 @ X23 @ X25 )
      | ( ( k4_xboole_0 @ X23 @ X25 )
       != X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('35',plain,
    ( ( sk_C_1 != sk_C_1 )
    | ( r1_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ sk_B @ sk_B ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('38',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( r2_hidden @ sk_D @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','40'])).

thf('42',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    | ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['9','41'])).

thf('43',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('45',plain,(
    ~ ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = sk_B ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ( r1_xboole_0 @ X26 @ ( k4_xboole_0 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('56',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('60',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('61',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('65',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4yZxID85Yz
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.99/3.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.99/3.19  % Solved by: fo/fo7.sh
% 2.99/3.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.99/3.19  % done 3755 iterations in 2.739s
% 2.99/3.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.99/3.19  % SZS output start Refutation
% 2.99/3.19  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.99/3.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.99/3.19  thf(sk_A_type, type, sk_A: $i).
% 2.99/3.19  thf(sk_B_type, type, sk_B: $i).
% 2.99/3.19  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.99/3.19  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.99/3.19  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.99/3.19  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.99/3.19  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.99/3.19  thf(sk_D_type, type, sk_D: $i).
% 2.99/3.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.99/3.19  thf(t149_zfmisc_1, conjecture,
% 2.99/3.19    (![A:$i,B:$i,C:$i,D:$i]:
% 2.99/3.19     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.99/3.19         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.99/3.19       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.99/3.19  thf(zf_stmt_0, negated_conjecture,
% 2.99/3.19    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.99/3.19        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.99/3.19            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.99/3.19          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 2.99/3.19    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 2.99/3.19  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf(symmetry_r1_xboole_0, axiom,
% 2.99/3.19    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.99/3.19  thf('2', plain,
% 2.99/3.19      (![X2 : $i, X3 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.99/3.19      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.99/3.19  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 2.99/3.19      inference('sup-', [status(thm)], ['1', '2'])).
% 2.99/3.19  thf(t65_zfmisc_1, axiom,
% 2.99/3.19    (![A:$i,B:$i]:
% 2.99/3.19     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.99/3.19       ( ~( r2_hidden @ B @ A ) ) ))).
% 2.99/3.19  thf('4', plain,
% 2.99/3.19      (![X39 : $i, X40 : $i]:
% 2.99/3.19         (((k4_xboole_0 @ X39 @ (k1_tarski @ X40)) = (X39))
% 2.99/3.19          | (r2_hidden @ X40 @ X39))),
% 2.99/3.19      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.99/3.19  thf(t83_xboole_1, axiom,
% 2.99/3.19    (![A:$i,B:$i]:
% 2.99/3.19     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.99/3.19  thf('5', plain,
% 2.99/3.19      (![X23 : $i, X25 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X23 @ X25) | ((k4_xboole_0 @ X23 @ X25) != (X23)))),
% 2.99/3.19      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.99/3.19  thf('6', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         (((X0) != (X0))
% 2.99/3.19          | (r2_hidden @ X1 @ X0)
% 2.99/3.19          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['4', '5'])).
% 2.99/3.19  thf('7', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 2.99/3.19      inference('simplify', [status(thm)], ['6'])).
% 2.99/3.19  thf(t75_xboole_1, axiom,
% 2.99/3.19    (![A:$i,B:$i]:
% 2.99/3.19     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.99/3.19          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 2.99/3.19  thf('8', plain,
% 2.99/3.19      (![X21 : $i, X22 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X21 @ X22)
% 2.99/3.19          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ X22))),
% 2.99/3.19      inference('cnf', [status(esa)], [t75_xboole_1])).
% 2.99/3.19  thf('9', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 2.99/3.19          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['7', '8'])).
% 2.99/3.19  thf('10', plain,
% 2.99/3.19      (![X39 : $i, X40 : $i]:
% 2.99/3.19         (((k4_xboole_0 @ X39 @ (k1_tarski @ X40)) = (X39))
% 2.99/3.19          | (r2_hidden @ X40 @ X39))),
% 2.99/3.19      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 2.99/3.19  thf(t48_xboole_1, axiom,
% 2.99/3.19    (![A:$i,B:$i]:
% 2.99/3.19     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.99/3.19  thf('11', plain,
% 2.99/3.19      (![X15 : $i, X16 : $i]:
% 2.99/3.19         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 2.99/3.19           = (k3_xboole_0 @ X15 @ X16))),
% 2.99/3.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.99/3.19  thf('12', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         (((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ (k1_tarski @ X1)))
% 2.99/3.19          | (r2_hidden @ X1 @ X0))),
% 2.99/3.19      inference('sup+', [status(thm)], ['10', '11'])).
% 2.99/3.19  thf('13', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf('14', plain,
% 2.99/3.19      (![X23 : $i, X24 : $i]:
% 2.99/3.19         (((k4_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_xboole_0 @ X23 @ X24))),
% 2.99/3.19      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.99/3.19  thf('15', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1))),
% 2.99/3.19      inference('sup-', [status(thm)], ['13', '14'])).
% 2.99/3.19  thf('16', plain,
% 2.99/3.19      (![X15 : $i, X16 : $i]:
% 2.99/3.19         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 2.99/3.19           = (k3_xboole_0 @ X15 @ X16))),
% 2.99/3.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.99/3.19  thf('17', plain,
% 2.99/3.19      (((k4_xboole_0 @ sk_C_1 @ sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_B))),
% 2.99/3.19      inference('sup+', [status(thm)], ['15', '16'])).
% 2.99/3.19  thf(commutativity_k3_xboole_0, axiom,
% 2.99/3.19    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.99/3.19  thf('18', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.99/3.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.99/3.19  thf('19', plain,
% 2.99/3.19      (((k4_xboole_0 @ sk_C_1 @ sk_C_1) = (k3_xboole_0 @ sk_B @ sk_C_1))),
% 2.99/3.19      inference('demod', [status(thm)], ['17', '18'])).
% 2.99/3.19  thf('20', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 2.99/3.19      inference('sup-', [status(thm)], ['1', '2'])).
% 2.99/3.19  thf('21', plain,
% 2.99/3.19      (![X23 : $i, X24 : $i]:
% 2.99/3.19         (((k4_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_xboole_0 @ X23 @ X24))),
% 2.99/3.19      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.99/3.19  thf('22', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B))),
% 2.99/3.19      inference('sup-', [status(thm)], ['20', '21'])).
% 2.99/3.19  thf('23', plain,
% 2.99/3.19      (![X15 : $i, X16 : $i]:
% 2.99/3.19         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 2.99/3.19           = (k3_xboole_0 @ X15 @ X16))),
% 2.99/3.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.99/3.19  thf('24', plain,
% 2.99/3.19      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C_1))),
% 2.99/3.19      inference('sup+', [status(thm)], ['22', '23'])).
% 2.99/3.19  thf('25', plain,
% 2.99/3.19      (((k4_xboole_0 @ sk_C_1 @ sk_C_1) = (k4_xboole_0 @ sk_B @ sk_B))),
% 2.99/3.19      inference('demod', [status(thm)], ['19', '24'])).
% 2.99/3.19  thf('26', plain,
% 2.99/3.19      (![X15 : $i, X16 : $i]:
% 2.99/3.19         ((k4_xboole_0 @ X15 @ (k4_xboole_0 @ X15 @ X16))
% 2.99/3.19           = (k3_xboole_0 @ X15 @ X16))),
% 2.99/3.19      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.99/3.19  thf('27', plain,
% 2.99/3.19      (((k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_B @ sk_B))
% 2.99/3.19         = (k3_xboole_0 @ sk_C_1 @ sk_C_1))),
% 2.99/3.19      inference('sup+', [status(thm)], ['25', '26'])).
% 2.99/3.19  thf('28', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1))),
% 2.99/3.19      inference('sup-', [status(thm)], ['13', '14'])).
% 2.99/3.19  thf(t36_xboole_1, axiom,
% 2.99/3.19    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.99/3.19  thf('29', plain,
% 2.99/3.19      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 2.99/3.19      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.99/3.19  thf('30', plain, ((r1_tarski @ sk_C_1 @ sk_C_1)),
% 2.99/3.19      inference('sup+', [status(thm)], ['28', '29'])).
% 2.99/3.19  thf(t28_xboole_1, axiom,
% 2.99/3.19    (![A:$i,B:$i]:
% 2.99/3.19     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.99/3.19  thf('31', plain,
% 2.99/3.19      (![X11 : $i, X12 : $i]:
% 2.99/3.19         (((k3_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_tarski @ X11 @ X12))),
% 2.99/3.19      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.99/3.19  thf('32', plain, (((k3_xboole_0 @ sk_C_1 @ sk_C_1) = (sk_C_1))),
% 2.99/3.19      inference('sup-', [status(thm)], ['30', '31'])).
% 2.99/3.19  thf('33', plain,
% 2.99/3.19      (((k4_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_B @ sk_B)) = (sk_C_1))),
% 2.99/3.19      inference('demod', [status(thm)], ['27', '32'])).
% 2.99/3.19  thf('34', plain,
% 2.99/3.19      (![X23 : $i, X25 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X23 @ X25) | ((k4_xboole_0 @ X23 @ X25) != (X23)))),
% 2.99/3.19      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.99/3.19  thf('35', plain,
% 2.99/3.19      ((((sk_C_1) != (sk_C_1))
% 2.99/3.19        | (r1_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_B @ sk_B)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['33', '34'])).
% 2.99/3.19  thf('36', plain, ((r1_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ sk_B @ sk_B))),
% 2.99/3.19      inference('simplify', [status(thm)], ['35'])).
% 2.99/3.19  thf('37', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf(t3_xboole_0, axiom,
% 2.99/3.19    (![A:$i,B:$i]:
% 2.99/3.19     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.99/3.19            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.99/3.19       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.99/3.19            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.99/3.19  thf('38', plain,
% 2.99/3.19      (![X4 : $i, X6 : $i, X7 : $i]:
% 2.99/3.19         (~ (r2_hidden @ X6 @ X4)
% 2.99/3.19          | ~ (r2_hidden @ X6 @ X7)
% 2.99/3.19          | ~ (r1_xboole_0 @ X4 @ X7))),
% 2.99/3.19      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.99/3.19  thf('39', plain,
% 2.99/3.19      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['37', '38'])).
% 2.99/3.19  thf('40', plain, (~ (r2_hidden @ sk_D @ (k4_xboole_0 @ sk_B @ sk_B))),
% 2.99/3.19      inference('sup-', [status(thm)], ['36', '39'])).
% 2.99/3.19  thf('41', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         (~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ (k1_tarski @ X0)))
% 2.99/3.19          | (r2_hidden @ X0 @ sk_B))),
% 2.99/3.19      inference('sup-', [status(thm)], ['12', '40'])).
% 2.99/3.19  thf('42', plain,
% 2.99/3.19      (((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) | (r2_hidden @ sk_D @ sk_B))),
% 2.99/3.19      inference('sup-', [status(thm)], ['9', '41'])).
% 2.99/3.19  thf('43', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf('44', plain,
% 2.99/3.19      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 2.99/3.19      inference('sup-', [status(thm)], ['37', '38'])).
% 2.99/3.19  thf('45', plain, (~ (r2_hidden @ sk_D @ sk_B)),
% 2.99/3.19      inference('sup-', [status(thm)], ['43', '44'])).
% 2.99/3.19  thf('46', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D))),
% 2.99/3.19      inference('clc', [status(thm)], ['42', '45'])).
% 2.99/3.19  thf('47', plain,
% 2.99/3.19      (![X23 : $i, X24 : $i]:
% 2.99/3.19         (((k4_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_xboole_0 @ X23 @ X24))),
% 2.99/3.19      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.99/3.19  thf('48', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (sk_B))),
% 2.99/3.19      inference('sup-', [status(thm)], ['46', '47'])).
% 2.99/3.19  thf('49', plain,
% 2.99/3.19      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 2.99/3.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.99/3.19  thf('50', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.99/3.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.99/3.19  thf('51', plain,
% 2.99/3.19      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 2.99/3.19      inference('demod', [status(thm)], ['49', '50'])).
% 2.99/3.19  thf(t85_xboole_1, axiom,
% 2.99/3.19    (![A:$i,B:$i,C:$i]:
% 2.99/3.19     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 2.99/3.19  thf('52', plain,
% 2.99/3.19      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.99/3.19         (~ (r1_tarski @ X26 @ X27)
% 2.99/3.19          | (r1_xboole_0 @ X26 @ (k4_xboole_0 @ X28 @ X27)))),
% 2.99/3.19      inference('cnf', [status(esa)], [t85_xboole_1])).
% 2.99/3.19  thf('53', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 2.99/3.19          (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['51', '52'])).
% 2.99/3.19  thf('54', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 2.99/3.19      inference('sup+', [status(thm)], ['48', '53'])).
% 2.99/3.19  thf('55', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.99/3.19      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.99/3.19  thf('56', plain,
% 2.99/3.19      (![X21 : $i, X22 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X21 @ X22)
% 2.99/3.19          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ X22))),
% 2.99/3.19      inference('cnf', [status(esa)], [t75_xboole_1])).
% 2.99/3.19  thf('57', plain,
% 2.99/3.19      (![X0 : $i, X1 : $i]:
% 2.99/3.19         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 2.99/3.19          | (r1_xboole_0 @ X0 @ X1))),
% 2.99/3.19      inference('sup-', [status(thm)], ['55', '56'])).
% 2.99/3.19  thf('58', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 2.99/3.19      inference('sup-', [status(thm)], ['54', '57'])).
% 2.99/3.19  thf('59', plain,
% 2.99/3.19      (![X2 : $i, X3 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.99/3.19      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.99/3.19  thf('60', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 2.99/3.19      inference('sup-', [status(thm)], ['58', '59'])).
% 2.99/3.19  thf(t70_xboole_1, axiom,
% 2.99/3.19    (![A:$i,B:$i,C:$i]:
% 2.99/3.19     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.99/3.19            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.99/3.19       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.99/3.19            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 2.99/3.19  thf('61', plain,
% 2.99/3.19      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 2.99/3.19          | ~ (r1_xboole_0 @ X17 @ X18)
% 2.99/3.19          | ~ (r1_xboole_0 @ X17 @ X19))),
% 2.99/3.19      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.99/3.19  thf('62', plain,
% 2.99/3.19      (![X0 : $i]:
% 2.99/3.19         (~ (r1_xboole_0 @ sk_B @ X0)
% 2.99/3.19          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 2.99/3.19      inference('sup-', [status(thm)], ['60', '61'])).
% 2.99/3.19  thf('63', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 2.99/3.19      inference('sup-', [status(thm)], ['3', '62'])).
% 2.99/3.19  thf('64', plain,
% 2.99/3.19      (![X2 : $i, X3 : $i]:
% 2.99/3.19         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.99/3.19      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.99/3.19  thf('65', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.99/3.19      inference('sup-', [status(thm)], ['63', '64'])).
% 2.99/3.19  thf('66', plain, ($false), inference('demod', [status(thm)], ['0', '65'])).
% 2.99/3.19  
% 2.99/3.19  % SZS output end Refutation
% 2.99/3.19  
% 3.04/3.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
