%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5Fl9maMvNf

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:05 EST 2020

% Result     : Theorem 4.04s
% Output     : Refutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 263 expanded)
%              Number of leaves         :   23 (  94 expanded)
%              Depth                    :   22
%              Number of atoms          :  547 (1890 expanded)
%              Number of equality atoms :   54 ( 182 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t144_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X30 @ X31 )
      | ( r1_xboole_0 @ ( k2_tarski @ X30 @ X32 ) @ X31 )
      | ( r2_hidden @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_tarski @ X2 @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_tarski @ X2 @ X1 ) )
        = X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','53'])).

thf('55',plain,(
    sk_C_1
 != ( k4_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( sk_C_1 != sk_C_1 )
    | ( r2_hidden @ sk_B_1 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r2_hidden @ sk_B_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r2_hidden @ sk_B_1 @ sk_C_1 ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5Fl9maMvNf
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.04/4.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.04/4.24  % Solved by: fo/fo7.sh
% 4.04/4.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.04/4.24  % done 6491 iterations in 3.777s
% 4.04/4.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.04/4.24  % SZS output start Refutation
% 4.04/4.24  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.04/4.24  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.04/4.24  thf(sk_B_type, type, sk_B: $i > $i).
% 4.04/4.24  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.04/4.24  thf(sk_A_type, type, sk_A: $i).
% 4.04/4.24  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.04/4.24  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.04/4.24  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.04/4.24  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.04/4.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.04/4.24  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.04/4.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.04/4.24  thf(t144_zfmisc_1, conjecture,
% 4.04/4.24    (![A:$i,B:$i,C:$i]:
% 4.04/4.24     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 4.04/4.24          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 4.04/4.24  thf(zf_stmt_0, negated_conjecture,
% 4.04/4.24    (~( ![A:$i,B:$i,C:$i]:
% 4.04/4.24        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 4.04/4.24             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 4.04/4.24    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 4.04/4.24  thf('0', plain, (~ (r2_hidden @ sk_B_1 @ sk_C_1)),
% 4.04/4.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.24  thf(t57_zfmisc_1, axiom,
% 4.04/4.24    (![A:$i,B:$i,C:$i]:
% 4.04/4.24     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 4.04/4.24          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 4.04/4.24  thf('1', plain,
% 4.04/4.24      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.04/4.24         ((r2_hidden @ X30 @ X31)
% 4.04/4.24          | (r1_xboole_0 @ (k2_tarski @ X30 @ X32) @ X31)
% 4.04/4.24          | (r2_hidden @ X32 @ X31))),
% 4.04/4.24      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 4.04/4.24  thf(t7_xboole_0, axiom,
% 4.04/4.24    (![A:$i]:
% 4.04/4.24     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 4.04/4.24          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 4.04/4.24  thf('2', plain,
% 4.04/4.24      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 4.04/4.24      inference('cnf', [status(esa)], [t7_xboole_0])).
% 4.04/4.24  thf(t4_xboole_0, axiom,
% 4.04/4.24    (![A:$i,B:$i]:
% 4.04/4.24     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 4.04/4.24            ( r1_xboole_0 @ A @ B ) ) ) & 
% 4.04/4.24       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 4.04/4.24            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 4.04/4.24  thf('3', plain,
% 4.04/4.24      (![X2 : $i, X4 : $i, X5 : $i]:
% 4.04/4.24         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 4.04/4.24          | ~ (r1_xboole_0 @ X2 @ X5))),
% 4.04/4.24      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.04/4.24  thf('4', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i]:
% 4.04/4.24         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 4.04/4.24      inference('sup-', [status(thm)], ['2', '3'])).
% 4.04/4.24  thf('5', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.04/4.24         ((r2_hidden @ X1 @ X0)
% 4.04/4.24          | (r2_hidden @ X2 @ X0)
% 4.04/4.24          | ((k3_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) = (k1_xboole_0)))),
% 4.04/4.24      inference('sup-', [status(thm)], ['1', '4'])).
% 4.04/4.24  thf(commutativity_k3_xboole_0, axiom,
% 4.04/4.24    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.04/4.24  thf('6', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.04/4.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.04/4.24  thf(t100_xboole_1, axiom,
% 4.04/4.24    (![A:$i,B:$i]:
% 4.04/4.24     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.04/4.24  thf('7', plain,
% 4.04/4.24      (![X10 : $i, X11 : $i]:
% 4.04/4.24         ((k4_xboole_0 @ X10 @ X11)
% 4.04/4.24           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 4.04/4.24      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.04/4.24  thf('8', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i]:
% 4.04/4.24         ((k4_xboole_0 @ X0 @ X1)
% 4.04/4.24           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 4.04/4.24      inference('sup+', [status(thm)], ['6', '7'])).
% 4.04/4.24  thf('9', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.04/4.24         (((k4_xboole_0 @ X0 @ (k2_tarski @ X2 @ X1))
% 4.04/4.24            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 4.04/4.24          | (r2_hidden @ X2 @ X0)
% 4.04/4.24          | (r2_hidden @ X1 @ X0))),
% 4.04/4.24      inference('sup+', [status(thm)], ['5', '8'])).
% 4.04/4.24  thf(t48_xboole_1, axiom,
% 4.04/4.24    (![A:$i,B:$i]:
% 4.04/4.24     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.04/4.24  thf('10', plain,
% 4.04/4.24      (![X16 : $i, X17 : $i]:
% 4.04/4.24         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 4.04/4.24           = (k3_xboole_0 @ X16 @ X17))),
% 4.04/4.24      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.04/4.24  thf(t36_xboole_1, axiom,
% 4.04/4.24    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 4.04/4.24  thf('11', plain,
% 4.04/4.24      (![X14 : $i, X15 : $i]: (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X14)),
% 4.04/4.24      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.04/4.24  thf('12', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 4.04/4.24      inference('sup+', [status(thm)], ['10', '11'])).
% 4.04/4.24  thf(l32_xboole_1, axiom,
% 4.04/4.24    (![A:$i,B:$i]:
% 4.04/4.24     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.04/4.24  thf('13', plain,
% 4.04/4.24      (![X7 : $i, X9 : $i]:
% 4.04/4.24         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 4.04/4.24      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.04/4.24  thf('14', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i]:
% 4.04/4.24         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 4.04/4.24      inference('sup-', [status(thm)], ['12', '13'])).
% 4.04/4.24  thf(t49_xboole_1, axiom,
% 4.04/4.24    (![A:$i,B:$i,C:$i]:
% 4.04/4.24     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 4.04/4.24       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 4.04/4.24  thf('15', plain,
% 4.04/4.24      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.04/4.24         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 4.04/4.24           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 4.04/4.24      inference('cnf', [status(esa)], [t49_xboole_1])).
% 4.04/4.24  thf('16', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i]:
% 4.04/4.24         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 4.04/4.24      inference('demod', [status(thm)], ['14', '15'])).
% 4.04/4.24  thf('17', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 4.04/4.24      inference('sup+', [status(thm)], ['10', '11'])).
% 4.04/4.24  thf('18', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.04/4.24      inference('sup+', [status(thm)], ['16', '17'])).
% 4.04/4.24  thf('19', plain,
% 4.04/4.24      (![X7 : $i, X9 : $i]:
% 4.04/4.24         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 4.04/4.24      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.04/4.24  thf('20', plain,
% 4.04/4.24      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.04/4.24      inference('sup-', [status(thm)], ['18', '19'])).
% 4.04/4.24  thf('21', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i]:
% 4.04/4.24         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 4.04/4.24      inference('demod', [status(thm)], ['14', '15'])).
% 4.04/4.24  thf('22', plain,
% 4.04/4.24      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.04/4.24      inference('sup+', [status(thm)], ['20', '21'])).
% 4.04/4.24  thf('23', plain,
% 4.04/4.24      (![X10 : $i, X11 : $i]:
% 4.04/4.24         ((k4_xboole_0 @ X10 @ X11)
% 4.04/4.24           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 4.04/4.24      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.04/4.24  thf('24', plain,
% 4.04/4.24      (![X0 : $i]:
% 4.04/4.24         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 4.04/4.24      inference('sup+', [status(thm)], ['22', '23'])).
% 4.04/4.24  thf('25', plain,
% 4.04/4.24      (![X16 : $i, X17 : $i]:
% 4.04/4.24         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 4.04/4.24           = (k3_xboole_0 @ X16 @ X17))),
% 4.04/4.24      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.04/4.24  thf('26', plain,
% 4.04/4.24      (![X0 : $i]:
% 4.04/4.24         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 4.04/4.24           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 4.04/4.24      inference('sup+', [status(thm)], ['24', '25'])).
% 4.04/4.24  thf('27', plain,
% 4.04/4.24      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.04/4.24      inference('sup+', [status(thm)], ['20', '21'])).
% 4.04/4.24  thf('28', plain,
% 4.04/4.24      (![X0 : $i]:
% 4.04/4.24         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 4.04/4.24      inference('demod', [status(thm)], ['26', '27'])).
% 4.04/4.24  thf('29', plain,
% 4.04/4.24      (![X7 : $i, X8 : $i]:
% 4.04/4.24         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 4.04/4.24      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.04/4.24  thf('30', plain,
% 4.04/4.24      (![X0 : $i]:
% 4.04/4.24         (((k1_xboole_0) != (k1_xboole_0))
% 4.04/4.24          | (r1_tarski @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 4.04/4.24      inference('sup-', [status(thm)], ['28', '29'])).
% 4.04/4.24  thf('31', plain,
% 4.04/4.24      (![X0 : $i]: (r1_tarski @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 4.04/4.24      inference('simplify', [status(thm)], ['30'])).
% 4.04/4.24  thf(t28_xboole_1, axiom,
% 4.04/4.24    (![A:$i,B:$i]:
% 4.04/4.24     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.04/4.24  thf('32', plain,
% 4.04/4.24      (![X12 : $i, X13 : $i]:
% 4.04/4.24         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 4.04/4.24      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.04/4.24  thf('33', plain,
% 4.04/4.24      (![X0 : $i]:
% 4.04/4.24         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 4.04/4.24      inference('sup-', [status(thm)], ['31', '32'])).
% 4.04/4.24  thf('34', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.04/4.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.04/4.24  thf('35', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 4.04/4.24      inference('sup+', [status(thm)], ['10', '11'])).
% 4.04/4.24  thf('36', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 4.04/4.24      inference('sup+', [status(thm)], ['34', '35'])).
% 4.04/4.24  thf('37', plain,
% 4.04/4.24      (![X7 : $i, X9 : $i]:
% 4.04/4.24         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 4.04/4.24      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.04/4.24  thf('38', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i]:
% 4.04/4.24         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 4.04/4.24      inference('sup-', [status(thm)], ['36', '37'])).
% 4.04/4.24  thf('39', plain,
% 4.04/4.24      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.04/4.24         ((k3_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X20))
% 4.04/4.24           = (k4_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20))),
% 4.04/4.24      inference('cnf', [status(esa)], [t49_xboole_1])).
% 4.04/4.24  thf('40', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i]:
% 4.04/4.24         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 4.04/4.24      inference('demod', [status(thm)], ['38', '39'])).
% 4.04/4.24  thf('41', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.04/4.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.04/4.24  thf('42', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i]:
% 4.04/4.24         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))),
% 4.04/4.24      inference('sup+', [status(thm)], ['40', '41'])).
% 4.04/4.24  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 4.04/4.24      inference('sup+', [status(thm)], ['33', '42'])).
% 4.04/4.24  thf('44', plain,
% 4.04/4.24      (![X16 : $i, X17 : $i]:
% 4.04/4.24         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 4.04/4.24           = (k3_xboole_0 @ X16 @ X17))),
% 4.04/4.24      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.04/4.24  thf('45', plain,
% 4.04/4.24      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 4.04/4.24      inference('sup+', [status(thm)], ['43', '44'])).
% 4.04/4.24  thf('46', plain,
% 4.04/4.24      (![X0 : $i]:
% 4.04/4.24         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 4.04/4.24      inference('sup+', [status(thm)], ['22', '23'])).
% 4.04/4.24  thf('47', plain,
% 4.04/4.24      (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 4.04/4.24      inference('demod', [status(thm)], ['45', '46'])).
% 4.04/4.24  thf('48', plain,
% 4.04/4.24      (![X0 : $i]:
% 4.04/4.24         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 4.04/4.24      inference('sup-', [status(thm)], ['31', '32'])).
% 4.04/4.24  thf('49', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 4.04/4.24      inference('sup+', [status(thm)], ['10', '11'])).
% 4.04/4.24  thf('50', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 4.04/4.24      inference('sup+', [status(thm)], ['48', '49'])).
% 4.04/4.24  thf('51', plain,
% 4.04/4.24      (![X12 : $i, X13 : $i]:
% 4.04/4.24         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 4.04/4.24      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.04/4.24  thf('52', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 4.04/4.24      inference('sup-', [status(thm)], ['50', '51'])).
% 4.04/4.24  thf('53', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 4.04/4.24      inference('sup+', [status(thm)], ['47', '52'])).
% 4.04/4.24  thf('54', plain,
% 4.04/4.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.04/4.24         (((k4_xboole_0 @ X0 @ (k2_tarski @ X2 @ X1)) = (X0))
% 4.04/4.24          | (r2_hidden @ X2 @ X0)
% 4.04/4.24          | (r2_hidden @ X1 @ X0))),
% 4.04/4.24      inference('demod', [status(thm)], ['9', '53'])).
% 4.04/4.24  thf('55', plain,
% 4.04/4.24      (((sk_C_1) != (k4_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B_1)))),
% 4.04/4.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.24  thf('56', plain,
% 4.04/4.24      ((((sk_C_1) != (sk_C_1))
% 4.04/4.24        | (r2_hidden @ sk_B_1 @ sk_C_1)
% 4.04/4.24        | (r2_hidden @ sk_A @ sk_C_1))),
% 4.04/4.24      inference('sup-', [status(thm)], ['54', '55'])).
% 4.04/4.24  thf('57', plain,
% 4.04/4.24      (((r2_hidden @ sk_A @ sk_C_1) | (r2_hidden @ sk_B_1 @ sk_C_1))),
% 4.04/4.24      inference('simplify', [status(thm)], ['56'])).
% 4.04/4.24  thf('58', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 4.04/4.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.04/4.24  thf('59', plain, ((r2_hidden @ sk_B_1 @ sk_C_1)),
% 4.04/4.24      inference('clc', [status(thm)], ['57', '58'])).
% 4.04/4.24  thf('60', plain, ($false), inference('demod', [status(thm)], ['0', '59'])).
% 4.04/4.24  
% 4.04/4.24  % SZS output end Refutation
% 4.04/4.24  
% 4.04/4.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
