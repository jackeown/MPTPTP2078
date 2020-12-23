%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O5D3KF2vXb

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:05 EST 2020

% Result     : Theorem 2.45s
% Output     : Refutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 148 expanded)
%              Number of leaves         :   26 (  57 expanded)
%              Depth                    :   17
%              Number of atoms          :  583 (1128 expanded)
%              Number of equality atoms :   57 (  91 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ X33 @ X34 )
      | ( r1_xboole_0 @ ( k2_tarski @ X33 @ X35 ) @ X34 )
      | ( r2_hidden @ X35 @ X34 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
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

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X22 @ X23 ) @ X23 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X9 @ X11 ) @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','39'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17 = X16 )
      | ( ( k4_xboole_0 @ X17 @ X16 )
       != ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
       != k1_xboole_0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['24','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('47',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_tarski @ X2 @ X1 ) )
        = X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','50'])).

thf('52',plain,(
    sk_C_1
 != ( k4_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_C_1 != sk_C_1 )
    | ( r2_hidden @ sk_B_1 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r2_hidden @ sk_B_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    r2_hidden @ sk_B_1 @ sk_C_1 ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['0','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.O5D3KF2vXb
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.45/2.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.45/2.69  % Solved by: fo/fo7.sh
% 2.45/2.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.45/2.69  % done 4173 iterations in 2.245s
% 2.45/2.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.45/2.69  % SZS output start Refutation
% 2.45/2.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.45/2.69  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.45/2.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.45/2.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.45/2.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.45/2.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.45/2.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.45/2.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.45/2.69  thf(sk_B_type, type, sk_B: $i > $i).
% 2.45/2.69  thf(sk_A_type, type, sk_A: $i).
% 2.45/2.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.45/2.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.45/2.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.45/2.69  thf(t144_zfmisc_1, conjecture,
% 2.45/2.69    (![A:$i,B:$i,C:$i]:
% 2.45/2.69     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 2.45/2.69          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 2.45/2.69  thf(zf_stmt_0, negated_conjecture,
% 2.45/2.69    (~( ![A:$i,B:$i,C:$i]:
% 2.45/2.69        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 2.45/2.69             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 2.45/2.69    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 2.45/2.69  thf('0', plain, (~ (r2_hidden @ sk_B_1 @ sk_C_1)),
% 2.45/2.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.69  thf(t57_zfmisc_1, axiom,
% 2.45/2.69    (![A:$i,B:$i,C:$i]:
% 2.45/2.69     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 2.45/2.69          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 2.45/2.69  thf('1', plain,
% 2.45/2.69      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.45/2.69         ((r2_hidden @ X33 @ X34)
% 2.45/2.69          | (r1_xboole_0 @ (k2_tarski @ X33 @ X35) @ X34)
% 2.45/2.69          | (r2_hidden @ X35 @ X34))),
% 2.45/2.69      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 2.45/2.69  thf(t7_xboole_0, axiom,
% 2.45/2.69    (![A:$i]:
% 2.45/2.69     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.45/2.69          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.45/2.69  thf('2', plain,
% 2.45/2.69      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 2.45/2.69      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.45/2.69  thf(t4_xboole_0, axiom,
% 2.45/2.69    (![A:$i,B:$i]:
% 2.45/2.69     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.45/2.69            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.45/2.69       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.45/2.69            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.45/2.69  thf('3', plain,
% 2.45/2.69      (![X2 : $i, X4 : $i, X5 : $i]:
% 2.45/2.69         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 2.45/2.69          | ~ (r1_xboole_0 @ X2 @ X5))),
% 2.45/2.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.45/2.69  thf('4', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i]:
% 2.45/2.69         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.45/2.69      inference('sup-', [status(thm)], ['2', '3'])).
% 2.45/2.69  thf('5', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.69         ((r2_hidden @ X1 @ X0)
% 2.45/2.69          | (r2_hidden @ X2 @ X0)
% 2.45/2.69          | ((k3_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) = (k1_xboole_0)))),
% 2.45/2.69      inference('sup-', [status(thm)], ['1', '4'])).
% 2.45/2.69  thf(commutativity_k3_xboole_0, axiom,
% 2.45/2.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.45/2.69  thf('6', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.45/2.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.45/2.69  thf(t100_xboole_1, axiom,
% 2.45/2.69    (![A:$i,B:$i]:
% 2.45/2.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.45/2.69  thf('7', plain,
% 2.45/2.69      (![X7 : $i, X8 : $i]:
% 2.45/2.69         ((k4_xboole_0 @ X7 @ X8)
% 2.45/2.69           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 2.45/2.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.45/2.69  thf('8', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i]:
% 2.45/2.69         ((k4_xboole_0 @ X0 @ X1)
% 2.45/2.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.45/2.69      inference('sup+', [status(thm)], ['6', '7'])).
% 2.45/2.69  thf('9', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.69         (((k4_xboole_0 @ X0 @ (k2_tarski @ X2 @ X1))
% 2.45/2.69            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 2.45/2.69          | (r2_hidden @ X2 @ X0)
% 2.45/2.69          | (r2_hidden @ X1 @ X0))),
% 2.45/2.69      inference('sup+', [status(thm)], ['5', '8'])).
% 2.45/2.69  thf(t79_xboole_1, axiom,
% 2.45/2.69    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 2.45/2.69  thf('10', plain,
% 2.45/2.69      (![X22 : $i, X23 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X22 @ X23) @ X23)),
% 2.45/2.69      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.45/2.69  thf('11', plain,
% 2.45/2.69      (![X2 : $i, X3 : $i]:
% 2.45/2.69         ((r1_xboole_0 @ X2 @ X3)
% 2.45/2.69          | (r2_hidden @ (sk_C @ X3 @ X2) @ (k3_xboole_0 @ X2 @ X3)))),
% 2.45/2.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.45/2.69  thf('12', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.45/2.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.45/2.69  thf('13', plain,
% 2.45/2.69      (![X2 : $i, X4 : $i, X5 : $i]:
% 2.45/2.69         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 2.45/2.69          | ~ (r1_xboole_0 @ X2 @ X5))),
% 2.45/2.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.45/2.69  thf('14', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.69         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 2.45/2.69          | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.45/2.69      inference('sup-', [status(thm)], ['12', '13'])).
% 2.45/2.69  thf('15', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i]:
% 2.45/2.69         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.45/2.69      inference('sup-', [status(thm)], ['11', '14'])).
% 2.45/2.69  thf('16', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.45/2.69      inference('sup-', [status(thm)], ['10', '15'])).
% 2.45/2.69  thf('17', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i]:
% 2.45/2.69         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.45/2.69      inference('sup-', [status(thm)], ['2', '3'])).
% 2.45/2.69  thf('18', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i]:
% 2.45/2.69         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.45/2.69      inference('sup-', [status(thm)], ['16', '17'])).
% 2.45/2.69  thf(t17_xboole_1, axiom,
% 2.45/2.69    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.45/2.69  thf('19', plain,
% 2.45/2.69      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 2.45/2.69      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.45/2.69  thf('20', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.45/2.69      inference('sup+', [status(thm)], ['18', '19'])).
% 2.45/2.69  thf(t28_xboole_1, axiom,
% 2.45/2.69    (![A:$i,B:$i]:
% 2.45/2.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.45/2.69  thf('21', plain,
% 2.45/2.69      (![X14 : $i, X15 : $i]:
% 2.45/2.69         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 2.45/2.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.45/2.69  thf('22', plain,
% 2.45/2.69      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.45/2.69      inference('sup-', [status(thm)], ['20', '21'])).
% 2.45/2.69  thf('23', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.45/2.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.45/2.69  thf('24', plain,
% 2.45/2.69      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.45/2.69      inference('sup+', [status(thm)], ['22', '23'])).
% 2.45/2.69  thf(t36_xboole_1, axiom,
% 2.45/2.69    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.45/2.69  thf('25', plain,
% 2.45/2.69      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 2.45/2.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.45/2.69  thf('26', plain,
% 2.45/2.69      (![X14 : $i, X15 : $i]:
% 2.45/2.69         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 2.45/2.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.45/2.69  thf('27', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i]:
% 2.45/2.69         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 2.45/2.69           = (k4_xboole_0 @ X0 @ X1))),
% 2.45/2.69      inference('sup-', [status(thm)], ['25', '26'])).
% 2.45/2.69  thf('28', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.45/2.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.45/2.69  thf('29', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i]:
% 2.45/2.69         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.45/2.69           = (k4_xboole_0 @ X0 @ X1))),
% 2.45/2.69      inference('demod', [status(thm)], ['27', '28'])).
% 2.45/2.69  thf('30', plain,
% 2.45/2.69      (![X7 : $i, X8 : $i]:
% 2.45/2.69         ((k4_xboole_0 @ X7 @ X8)
% 2.45/2.69           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 2.45/2.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.45/2.69  thf('31', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.45/2.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.45/2.69  thf(t112_xboole_1, axiom,
% 2.45/2.69    (![A:$i,B:$i,C:$i]:
% 2.45/2.69     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 2.45/2.69       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 2.45/2.69  thf('32', plain,
% 2.45/2.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.45/2.69         ((k5_xboole_0 @ (k3_xboole_0 @ X9 @ X11) @ (k3_xboole_0 @ X10 @ X11))
% 2.45/2.69           = (k3_xboole_0 @ (k5_xboole_0 @ X9 @ X10) @ X11))),
% 2.45/2.69      inference('cnf', [status(esa)], [t112_xboole_1])).
% 2.45/2.69  thf('33', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.69         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 2.45/2.69           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 2.45/2.69      inference('sup+', [status(thm)], ['31', '32'])).
% 2.45/2.69  thf('34', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i]:
% 2.45/2.69         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 2.45/2.69           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)) @ X0))),
% 2.45/2.69      inference('sup+', [status(thm)], ['30', '33'])).
% 2.45/2.69  thf('35', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i]:
% 2.45/2.69         ((k4_xboole_0 @ X0 @ X1)
% 2.45/2.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.45/2.69      inference('sup+', [status(thm)], ['6', '7'])).
% 2.45/2.69  thf('36', plain,
% 2.45/2.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.45/2.70      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.45/2.70  thf('37', plain,
% 2.45/2.70      (![X0 : $i, X1 : $i]:
% 2.45/2.70         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 2.45/2.70           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.45/2.70      inference('demod', [status(thm)], ['34', '35', '36'])).
% 2.45/2.70  thf('38', plain,
% 2.45/2.70      (![X0 : $i, X1 : $i]:
% 2.45/2.70         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 2.45/2.70      inference('sup-', [status(thm)], ['16', '17'])).
% 2.45/2.70  thf('39', plain,
% 2.45/2.70      (![X0 : $i, X1 : $i]:
% 2.45/2.70         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 2.45/2.70      inference('demod', [status(thm)], ['37', '38'])).
% 2.45/2.70  thf('40', plain,
% 2.45/2.70      (![X0 : $i, X1 : $i]:
% 2.45/2.70         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 2.45/2.70      inference('sup+', [status(thm)], ['29', '39'])).
% 2.45/2.70  thf(t32_xboole_1, axiom,
% 2.45/2.70    (![A:$i,B:$i]:
% 2.45/2.70     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 2.45/2.70       ( ( A ) = ( B ) ) ))).
% 2.45/2.70  thf('41', plain,
% 2.45/2.70      (![X16 : $i, X17 : $i]:
% 2.45/2.70         (((X17) = (X16))
% 2.45/2.70          | ((k4_xboole_0 @ X17 @ X16) != (k4_xboole_0 @ X16 @ X17)))),
% 2.45/2.70      inference('cnf', [status(esa)], [t32_xboole_1])).
% 2.45/2.70  thf('42', plain,
% 2.45/2.70      (![X0 : $i, X1 : $i]:
% 2.45/2.70         (((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) != (k1_xboole_0))
% 2.45/2.70          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.45/2.70      inference('sup-', [status(thm)], ['40', '41'])).
% 2.45/2.70  thf(t48_xboole_1, axiom,
% 2.45/2.70    (![A:$i,B:$i]:
% 2.45/2.70     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.45/2.70  thf('43', plain,
% 2.45/2.70      (![X20 : $i, X21 : $i]:
% 2.45/2.70         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 2.45/2.70           = (k3_xboole_0 @ X20 @ X21))),
% 2.45/2.70      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.45/2.70  thf('44', plain,
% 2.45/2.70      (![X0 : $i, X1 : $i]:
% 2.45/2.70         (((k3_xboole_0 @ X0 @ X1) != (k1_xboole_0))
% 2.45/2.70          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.45/2.70      inference('demod', [status(thm)], ['42', '43'])).
% 2.45/2.70  thf('45', plain,
% 2.45/2.70      (![X0 : $i]:
% 2.45/2.70         (((k1_xboole_0) != (k1_xboole_0))
% 2.45/2.70          | ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 2.45/2.70      inference('sup-', [status(thm)], ['24', '44'])).
% 2.45/2.70  thf('46', plain,
% 2.45/2.70      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.45/2.70      inference('sup+', [status(thm)], ['22', '23'])).
% 2.45/2.70  thf('47', plain,
% 2.45/2.70      (![X7 : $i, X8 : $i]:
% 2.45/2.70         ((k4_xboole_0 @ X7 @ X8)
% 2.45/2.70           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 2.45/2.70      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.45/2.70  thf('48', plain,
% 2.45/2.70      (![X0 : $i]:
% 2.45/2.70         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.45/2.70      inference('sup+', [status(thm)], ['46', '47'])).
% 2.45/2.70  thf('49', plain,
% 2.45/2.70      (![X0 : $i]:
% 2.45/2.70         (((k1_xboole_0) != (k1_xboole_0))
% 2.45/2.70          | ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0)))),
% 2.45/2.70      inference('demod', [status(thm)], ['45', '48'])).
% 2.45/2.70  thf('50', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.45/2.70      inference('simplify', [status(thm)], ['49'])).
% 2.45/2.70  thf('51', plain,
% 2.45/2.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.45/2.70         (((k4_xboole_0 @ X0 @ (k2_tarski @ X2 @ X1)) = (X0))
% 2.45/2.70          | (r2_hidden @ X2 @ X0)
% 2.45/2.70          | (r2_hidden @ X1 @ X0))),
% 2.45/2.70      inference('demod', [status(thm)], ['9', '50'])).
% 2.45/2.70  thf('52', plain,
% 2.45/2.70      (((sk_C_1) != (k4_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B_1)))),
% 2.45/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.70  thf('53', plain,
% 2.45/2.70      ((((sk_C_1) != (sk_C_1))
% 2.45/2.70        | (r2_hidden @ sk_B_1 @ sk_C_1)
% 2.45/2.70        | (r2_hidden @ sk_A @ sk_C_1))),
% 2.45/2.70      inference('sup-', [status(thm)], ['51', '52'])).
% 2.45/2.70  thf('54', plain,
% 2.45/2.70      (((r2_hidden @ sk_A @ sk_C_1) | (r2_hidden @ sk_B_1 @ sk_C_1))),
% 2.45/2.70      inference('simplify', [status(thm)], ['53'])).
% 2.45/2.70  thf('55', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 2.45/2.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.45/2.70  thf('56', plain, ((r2_hidden @ sk_B_1 @ sk_C_1)),
% 2.45/2.70      inference('clc', [status(thm)], ['54', '55'])).
% 2.45/2.70  thf('57', plain, ($false), inference('demod', [status(thm)], ['0', '56'])).
% 2.45/2.70  
% 2.45/2.70  % SZS output end Refutation
% 2.45/2.70  
% 2.45/2.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
