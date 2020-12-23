%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Wey0iXTqwi

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:15 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 664 expanded)
%              Number of leaves         :   21 ( 252 expanded)
%              Depth                    :   16
%              Number of atoms          : 1310 (6318 expanded)
%              Number of equality atoms :  126 ( 627 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ X24 )
        = X24 )
      | ~ ( r2_hidden @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ sk_A ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ sk_C ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( r1_tarski @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_C @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( r1_tarski @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('19',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_tarski @ sk_D )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('24',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('26',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('28',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t25_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ C @ A ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ B @ C ) ) @ ( k2_xboole_0 @ C @ A ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) @ ( k3_xboole_0 @ X21 @ X19 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) @ ( k2_xboole_0 @ X21 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t25_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) @ ( k3_xboole_0 @ X21 @ X19 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X21 @ X19 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_tarski @ sk_D ) ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ) ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('37',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = sk_B ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_tarski @ sk_D ) ) @ ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 ) @ ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['34','37','38'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('41',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) @ ( k3_xboole_0 @ X21 @ X19 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X21 @ X19 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('48',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43','46','49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('54',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) @ ( k3_xboole_0 @ X21 @ X19 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X21 @ X19 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('60',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43','46','49','50','51'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('65',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('69',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','61','62','63','64','67','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','61','62','63','64','67','70'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43','46','49','50','51'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','71','72','73','74'])).

thf('76',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['21','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('82',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('84',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ sk_C ),
    inference('sup+',[status(thm)],['5','8'])).

thf('85',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('86',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('88',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('90',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','61','62','63','64','67','70'])).

thf('94',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('95',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('96',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('98',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('100',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = sk_A ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k1_tarski @ sk_D )
    = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','80','81','82','83','92','93','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('103',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('105',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('107',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('109',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('111',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','61','62','63','64','67','70'])).

thf('114',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('115',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k3_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('118',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['113','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['112','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['111','124'])).

thf('126',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['58','61','62','63','64','67','70'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) )
      = sk_B ) ),
    inference('sup+',[status(thm)],['102','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['42','43','46','49','50','51'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_A )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_A )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k1_tarski @ sk_D )
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['101','134'])).

thf('136',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('138',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['135','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Wey0iXTqwi
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.35/1.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.35/1.56  % Solved by: fo/fo7.sh
% 1.35/1.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.56  % done 1604 iterations in 1.065s
% 1.35/1.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.35/1.56  % SZS output start Refutation
% 1.35/1.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.35/1.56  thf(sk_B_type, type, sk_B: $i).
% 1.35/1.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.35/1.56  thf(sk_C_type, type, sk_C: $i).
% 1.35/1.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.35/1.56  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.35/1.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.35/1.56  thf(sk_D_type, type, sk_D: $i).
% 1.35/1.56  thf(t148_zfmisc_1, conjecture,
% 1.35/1.56    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.56     ( ( ( r1_tarski @ A @ B ) & 
% 1.35/1.56         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.35/1.56         ( r2_hidden @ D @ A ) ) =>
% 1.35/1.56       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 1.35/1.56  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.56        ( ( ( r1_tarski @ A @ B ) & 
% 1.35/1.56            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.35/1.56            ( r2_hidden @ D @ A ) ) =>
% 1.35/1.56          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 1.35/1.56    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 1.35/1.56  thf('0', plain, ((r2_hidden @ sk_D @ sk_A)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf(t46_zfmisc_1, axiom,
% 1.35/1.56    (![A:$i,B:$i]:
% 1.35/1.56     ( ( r2_hidden @ A @ B ) =>
% 1.35/1.56       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 1.35/1.56  thf('1', plain,
% 1.35/1.56      (![X24 : $i, X25 : $i]:
% 1.35/1.56         (((k2_xboole_0 @ (k1_tarski @ X25) @ X24) = (X24))
% 1.35/1.56          | ~ (r2_hidden @ X25 @ X24))),
% 1.35/1.56      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 1.35/1.56  thf('2', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (sk_A))),
% 1.35/1.56      inference('sup-', [status(thm)], ['0', '1'])).
% 1.35/1.56  thf(t7_xboole_1, axiom,
% 1.35/1.56    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.35/1.56  thf('3', plain,
% 1.35/1.56      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 1.35/1.56      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.35/1.56  thf('4', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ sk_A)),
% 1.35/1.56      inference('sup+', [status(thm)], ['2', '3'])).
% 1.35/1.56  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf(commutativity_k3_xboole_0, axiom,
% 1.35/1.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.35/1.56  thf('6', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf(t17_xboole_1, axiom,
% 1.35/1.56    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.35/1.56  thf('7', plain,
% 1.35/1.56      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 1.35/1.56      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.35/1.56  thf('8', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.35/1.56      inference('sup+', [status(thm)], ['6', '7'])).
% 1.35/1.56  thf('9', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ sk_C)),
% 1.35/1.56      inference('sup+', [status(thm)], ['5', '8'])).
% 1.35/1.56  thf(t19_xboole_1, axiom,
% 1.35/1.56    (![A:$i,B:$i,C:$i]:
% 1.35/1.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.35/1.56       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.35/1.56  thf('10', plain,
% 1.35/1.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.35/1.56         (~ (r1_tarski @ X9 @ X10)
% 1.35/1.56          | ~ (r1_tarski @ X9 @ X11)
% 1.35/1.56          | (r1_tarski @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.35/1.56      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.35/1.56  thf('11', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         ((r1_tarski @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_C @ X0))
% 1.35/1.56          | ~ (r1_tarski @ (k1_tarski @ sk_D) @ X0))),
% 1.35/1.56      inference('sup-', [status(thm)], ['9', '10'])).
% 1.35/1.56  thf('12', plain,
% 1.35/1.56      ((r1_tarski @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_C @ sk_A))),
% 1.35/1.56      inference('sup-', [status(thm)], ['4', '11'])).
% 1.35/1.56  thf(d10_xboole_0, axiom,
% 1.35/1.56    (![A:$i,B:$i]:
% 1.35/1.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.35/1.56  thf('13', plain,
% 1.35/1.56      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 1.35/1.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.35/1.56  thf('14', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 1.35/1.56      inference('simplify', [status(thm)], ['13'])).
% 1.35/1.56  thf('15', plain,
% 1.35/1.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.35/1.56         (~ (r1_tarski @ X9 @ X10)
% 1.35/1.56          | ~ (r1_tarski @ X9 @ X11)
% 1.35/1.56          | (r1_tarski @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.35/1.56      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.35/1.56  thf('16', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 1.35/1.56      inference('sup-', [status(thm)], ['14', '15'])).
% 1.35/1.56  thf('17', plain,
% 1.35/1.56      ((r1_tarski @ (k1_tarski @ sk_D) @ 
% 1.35/1.56        (k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 1.35/1.56      inference('sup-', [status(thm)], ['12', '16'])).
% 1.35/1.56  thf('18', plain,
% 1.35/1.56      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 1.35/1.56      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.35/1.56  thf('19', plain,
% 1.35/1.56      (![X2 : $i, X4 : $i]:
% 1.35/1.56         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 1.35/1.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.35/1.56  thf('20', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.35/1.56          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.35/1.56      inference('sup-', [status(thm)], ['18', '19'])).
% 1.35/1.56  thf('21', plain,
% 1.35/1.56      (((k1_tarski @ sk_D)
% 1.35/1.56         = (k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 1.35/1.56      inference('sup-', [status(thm)], ['17', '20'])).
% 1.35/1.56  thf('22', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('23', plain,
% 1.35/1.56      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 1.35/1.56      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.35/1.56  thf('24', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ sk_B)),
% 1.35/1.56      inference('sup+', [status(thm)], ['22', '23'])).
% 1.35/1.56  thf(t12_xboole_1, axiom,
% 1.35/1.56    (![A:$i,B:$i]:
% 1.35/1.56     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.35/1.56  thf('25', plain,
% 1.35/1.56      (![X5 : $i, X6 : $i]:
% 1.35/1.56         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.35/1.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.35/1.56  thf('26', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (sk_B))),
% 1.35/1.56      inference('sup-', [status(thm)], ['24', '25'])).
% 1.35/1.56  thf(t21_xboole_1, axiom,
% 1.35/1.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.35/1.56  thf('27', plain,
% 1.35/1.56      (![X12 : $i, X13 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 1.35/1.56      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.35/1.56  thf('28', plain,
% 1.35/1.56      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_tarski @ sk_D))),
% 1.35/1.56      inference('sup+', [status(thm)], ['26', '27'])).
% 1.35/1.56  thf('29', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('30', plain,
% 1.35/1.56      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (k1_tarski @ sk_D))),
% 1.35/1.56      inference('demod', [status(thm)], ['28', '29'])).
% 1.35/1.56  thf(t25_xboole_1, axiom,
% 1.35/1.56    (![A:$i,B:$i,C:$i]:
% 1.35/1.56     ( ( k2_xboole_0 @
% 1.35/1.56         ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ B @ C ) ) @ 
% 1.35/1.56         ( k3_xboole_0 @ C @ A ) ) =
% 1.35/1.56       ( k3_xboole_0 @
% 1.35/1.56         ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ B @ C ) ) @ 
% 1.35/1.56         ( k2_xboole_0 @ C @ A ) ) ))).
% 1.35/1.56  thf('31', plain,
% 1.35/1.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ 
% 1.35/1.56           (k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k3_xboole_0 @ X20 @ X21)) @ 
% 1.35/1.56           (k3_xboole_0 @ X21 @ X19))
% 1.35/1.56           = (k3_xboole_0 @ 
% 1.35/1.56              (k3_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ 
% 1.35/1.56               (k2_xboole_0 @ X20 @ X21)) @ 
% 1.35/1.56              (k2_xboole_0 @ X21 @ X19)))),
% 1.35/1.56      inference('cnf', [status(esa)], [t25_xboole_1])).
% 1.35/1.56  thf('32', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('33', plain,
% 1.35/1.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ 
% 1.35/1.56           (k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k3_xboole_0 @ X20 @ X21)) @ 
% 1.35/1.56           (k3_xboole_0 @ X21 @ X19))
% 1.35/1.56           = (k3_xboole_0 @ (k2_xboole_0 @ X21 @ X19) @ 
% 1.35/1.56              (k3_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ 
% 1.35/1.56               (k2_xboole_0 @ X20 @ X21))))),
% 1.35/1.56      inference('demod', [status(thm)], ['31', '32'])).
% 1.35/1.56  thf('34', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ 
% 1.35/1.56           (k2_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ (k1_tarski @ sk_D)) @ 
% 1.35/1.56           (k3_xboole_0 @ (k1_tarski @ sk_D) @ X0))
% 1.35/1.56           = (k3_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_D) @ X0) @ 
% 1.35/1.56              (k3_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ 
% 1.35/1.56               (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_D)))))),
% 1.35/1.56      inference('sup+', [status(thm)], ['30', '33'])).
% 1.35/1.56  thf('35', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf(t22_xboole_1, axiom,
% 1.35/1.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.35/1.56  thf('36', plain,
% 1.35/1.56      (![X14 : $i, X15 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 1.35/1.56      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.35/1.56  thf('37', plain, (((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (sk_B))),
% 1.35/1.56      inference('sup+', [status(thm)], ['35', '36'])).
% 1.35/1.56  thf('38', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('39', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ 
% 1.35/1.56           (k2_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ (k1_tarski @ sk_D)) @ 
% 1.35/1.56           (k3_xboole_0 @ (k1_tarski @ sk_D) @ X0))
% 1.35/1.56           = (k3_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_D) @ X0) @ 
% 1.35/1.56              (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ X0 @ sk_B))))),
% 1.35/1.56      inference('demod', [status(thm)], ['34', '37', '38'])).
% 1.35/1.56  thf(t23_xboole_1, axiom,
% 1.35/1.56    (![A:$i,B:$i,C:$i]:
% 1.35/1.56     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.35/1.56       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 1.35/1.56  thf('40', plain,
% 1.35/1.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 1.35/1.56           = (k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 1.35/1.56              (k3_xboole_0 @ X16 @ X18)))),
% 1.35/1.56      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.35/1.56  thf('41', plain,
% 1.35/1.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ 
% 1.35/1.56           (k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k3_xboole_0 @ X20 @ X21)) @ 
% 1.35/1.56           (k3_xboole_0 @ X21 @ X19))
% 1.35/1.56           = (k3_xboole_0 @ (k2_xboole_0 @ X21 @ X19) @ 
% 1.35/1.56              (k3_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ 
% 1.35/1.56               (k2_xboole_0 @ X20 @ X21))))),
% 1.35/1.56      inference('demod', [status(thm)], ['31', '32'])).
% 1.35/1.56  thf('42', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 1.35/1.56           (k3_xboole_0 @ X0 @ X1))
% 1.35/1.56           = (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ 
% 1.35/1.56              (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X1) @ (k2_xboole_0 @ X1 @ X0))))),
% 1.35/1.56      inference('sup+', [status(thm)], ['40', '41'])).
% 1.35/1.56  thf('43', plain,
% 1.35/1.56      (![X12 : $i, X13 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 1.35/1.56      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.35/1.56  thf('44', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('45', plain,
% 1.35/1.56      (![X14 : $i, X15 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 1.35/1.56      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.35/1.56  thf('46', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 1.35/1.56      inference('sup+', [status(thm)], ['44', '45'])).
% 1.35/1.56  thf('47', plain,
% 1.35/1.56      (![X12 : $i, X13 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 1.35/1.56      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.35/1.56  thf('48', plain,
% 1.35/1.56      (![X14 : $i, X15 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 1.35/1.56      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.35/1.56  thf('49', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.35/1.56      inference('sup+', [status(thm)], ['47', '48'])).
% 1.35/1.56  thf('50', plain,
% 1.35/1.56      (![X12 : $i, X13 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 1.35/1.56      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.35/1.56  thf('51', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('52', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.35/1.56      inference('demod', [status(thm)], ['42', '43', '46', '49', '50', '51'])).
% 1.35/1.56  thf('53', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('54', plain,
% 1.35/1.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ 
% 1.35/1.56           (k2_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ (k3_xboole_0 @ X20 @ X21)) @ 
% 1.35/1.56           (k3_xboole_0 @ X21 @ X19))
% 1.35/1.56           = (k3_xboole_0 @ (k2_xboole_0 @ X21 @ X19) @ 
% 1.35/1.56              (k3_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ 
% 1.35/1.56               (k2_xboole_0 @ X20 @ X21))))),
% 1.35/1.56      inference('demod', [status(thm)], ['31', '32'])).
% 1.35/1.56  thf('55', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ 
% 1.35/1.56           (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X2)) @ 
% 1.35/1.56           (k3_xboole_0 @ X2 @ X0))
% 1.35/1.56           = (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ 
% 1.35/1.56              (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X2))))),
% 1.35/1.56      inference('sup+', [status(thm)], ['53', '54'])).
% 1.35/1.56  thf('56', plain,
% 1.35/1.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 1.35/1.56           = (k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 1.35/1.56              (k3_xboole_0 @ X16 @ X18)))),
% 1.35/1.56      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.35/1.56  thf('57', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)) @ 
% 1.35/1.56           (k3_xboole_0 @ X2 @ X0))
% 1.35/1.56           = (k3_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ 
% 1.35/1.56              (k3_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X2))))),
% 1.35/1.56      inference('demod', [status(thm)], ['55', '56'])).
% 1.35/1.56  thf('58', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ 
% 1.35/1.56           (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))) @ 
% 1.35/1.56           (k3_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 1.35/1.56           = (k3_xboole_0 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ 
% 1.35/1.56              (k2_xboole_0 @ X1 @ X0)))),
% 1.35/1.56      inference('sup+', [status(thm)], ['52', '57'])).
% 1.35/1.56  thf('59', plain,
% 1.35/1.56      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 1.35/1.56      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.35/1.56  thf('60', plain,
% 1.35/1.56      (![X5 : $i, X6 : $i]:
% 1.35/1.56         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.35/1.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.35/1.56  thf('61', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.35/1.56           = (k2_xboole_0 @ X1 @ X0))),
% 1.35/1.56      inference('sup-', [status(thm)], ['59', '60'])).
% 1.35/1.56  thf('62', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.35/1.56      inference('demod', [status(thm)], ['42', '43', '46', '49', '50', '51'])).
% 1.35/1.56  thf('63', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('64', plain,
% 1.35/1.56      (![X12 : $i, X13 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 1.35/1.56      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.35/1.56  thf('65', plain,
% 1.35/1.56      (![X12 : $i, X13 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 1.35/1.56      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.35/1.56  thf('66', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 1.35/1.56      inference('sup+', [status(thm)], ['44', '45'])).
% 1.35/1.56  thf('67', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 1.35/1.56           = (k2_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('sup+', [status(thm)], ['65', '66'])).
% 1.35/1.56  thf('68', plain,
% 1.35/1.56      (![X14 : $i, X15 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 1.35/1.56      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.35/1.56  thf('69', plain,
% 1.35/1.56      (![X12 : $i, X13 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 1.35/1.56      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.35/1.56  thf('70', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.35/1.56      inference('sup+', [status(thm)], ['68', '69'])).
% 1.35/1.56  thf('71', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 1.35/1.56      inference('demod', [status(thm)],
% 1.35/1.56                ['58', '61', '62', '63', '64', '67', '70'])).
% 1.35/1.56  thf('72', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 1.35/1.56      inference('demod', [status(thm)],
% 1.35/1.56                ['58', '61', '62', '63', '64', '67', '70'])).
% 1.35/1.56  thf('73', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.35/1.56      inference('demod', [status(thm)], ['42', '43', '46', '49', '50', '51'])).
% 1.35/1.56  thf('74', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('75', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_D) @ X0) @ 
% 1.35/1.56           (k2_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ X0 @ sk_B)))
% 1.35/1.56           = (k3_xboole_0 @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_D) @ X0)))),
% 1.35/1.56      inference('demod', [status(thm)], ['39', '71', '72', '73', '74'])).
% 1.35/1.56  thf('76', plain,
% 1.35/1.56      (((k2_xboole_0 @ (k1_tarski @ sk_D) @ 
% 1.35/1.56         (k2_xboole_0 @ (k1_tarski @ sk_D) @ 
% 1.35/1.56          (k3_xboole_0 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B)))
% 1.35/1.56         = (k3_xboole_0 @ sk_B @ 
% 1.35/1.56            (k2_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_C @ sk_A))))),
% 1.35/1.56      inference('sup+', [status(thm)], ['21', '75'])).
% 1.35/1.56  thf('77', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('78', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('79', plain,
% 1.35/1.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 1.35/1.56           = (k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 1.35/1.56              (k3_xboole_0 @ X16 @ X18)))),
% 1.35/1.56      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.35/1.56  thf('80', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C @ X0))
% 1.35/1.56           = (k2_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ X0)))),
% 1.35/1.56      inference('sup+', [status(thm)], ['78', '79'])).
% 1.35/1.56  thf('81', plain,
% 1.35/1.56      (![X14 : $i, X15 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 1.35/1.56      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.35/1.56  thf('82', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('83', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.35/1.56      inference('sup+', [status(thm)], ['47', '48'])).
% 1.35/1.56  thf('84', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ sk_C)),
% 1.35/1.56      inference('sup+', [status(thm)], ['5', '8'])).
% 1.35/1.56  thf('85', plain,
% 1.35/1.56      (![X5 : $i, X6 : $i]:
% 1.35/1.56         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.35/1.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.35/1.56  thf('86', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D) @ sk_C) = (sk_C))),
% 1.35/1.56      inference('sup-', [status(thm)], ['84', '85'])).
% 1.35/1.56  thf('87', plain,
% 1.35/1.56      (![X12 : $i, X13 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 1.35/1.56      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.35/1.56  thf('88', plain,
% 1.35/1.56      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_C) = (k1_tarski @ sk_D))),
% 1.35/1.56      inference('sup+', [status(thm)], ['86', '87'])).
% 1.35/1.56  thf('89', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('90', plain,
% 1.35/1.56      (((k3_xboole_0 @ sk_C @ (k1_tarski @ sk_D)) = (k1_tarski @ sk_D))),
% 1.35/1.56      inference('demod', [status(thm)], ['88', '89'])).
% 1.35/1.56  thf('91', plain,
% 1.35/1.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 1.35/1.56           = (k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 1.35/1.56              (k3_xboole_0 @ X16 @ X18)))),
% 1.35/1.56      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.35/1.56  thf('92', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ sk_C @ (k2_xboole_0 @ (k1_tarski @ sk_D) @ X0))
% 1.35/1.56           = (k2_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_C @ X0)))),
% 1.35/1.56      inference('sup+', [status(thm)], ['90', '91'])).
% 1.35/1.56  thf('93', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 1.35/1.56      inference('demod', [status(thm)],
% 1.35/1.56                ['58', '61', '62', '63', '64', '67', '70'])).
% 1.35/1.56  thf('94', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (sk_A))),
% 1.35/1.56      inference('sup-', [status(thm)], ['0', '1'])).
% 1.35/1.56  thf('95', plain,
% 1.35/1.56      (![X12 : $i, X13 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 1.35/1.56      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.35/1.56  thf('96', plain,
% 1.35/1.56      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (k1_tarski @ sk_D))),
% 1.35/1.56      inference('sup+', [status(thm)], ['94', '95'])).
% 1.35/1.56  thf('97', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('98', plain,
% 1.35/1.56      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k1_tarski @ sk_D))),
% 1.35/1.56      inference('demod', [status(thm)], ['96', '97'])).
% 1.35/1.56  thf('99', plain,
% 1.35/1.56      (![X14 : $i, X15 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 1.35/1.56      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.35/1.56  thf('100', plain, (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (sk_A))),
% 1.35/1.56      inference('sup+', [status(thm)], ['98', '99'])).
% 1.35/1.56  thf('101', plain,
% 1.35/1.56      (((k1_tarski @ sk_D) = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 1.35/1.56      inference('demod', [status(thm)],
% 1.35/1.56                ['76', '77', '80', '81', '82', '83', '92', '93', '100'])).
% 1.35/1.56  thf('102', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('103', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('104', plain,
% 1.35/1.56      (![X5 : $i, X6 : $i]:
% 1.35/1.56         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.35/1.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.35/1.56  thf('105', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 1.35/1.56      inference('sup-', [status(thm)], ['103', '104'])).
% 1.35/1.56  thf('106', plain,
% 1.35/1.56      (![X12 : $i, X13 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 1.35/1.56      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.35/1.56  thf('107', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 1.35/1.56      inference('sup+', [status(thm)], ['105', '106'])).
% 1.35/1.56  thf('108', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('109', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 1.35/1.56      inference('demod', [status(thm)], ['107', '108'])).
% 1.35/1.56  thf('110', plain,
% 1.35/1.56      (![X14 : $i, X15 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 1.35/1.56      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.35/1.56  thf('111', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.35/1.56      inference('sup+', [status(thm)], ['109', '110'])).
% 1.35/1.56  thf('112', plain,
% 1.35/1.56      (![X14 : $i, X15 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)) = (X14))),
% 1.35/1.56      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.35/1.56  thf('113', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 1.35/1.56      inference('demod', [status(thm)],
% 1.35/1.56                ['58', '61', '62', '63', '64', '67', '70'])).
% 1.35/1.56  thf('114', plain,
% 1.35/1.56      (![X12 : $i, X13 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (X12))),
% 1.35/1.56      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.35/1.56  thf('115', plain,
% 1.35/1.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 1.35/1.56           = (k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ 
% 1.35/1.56              (k3_xboole_0 @ X16 @ X18)))),
% 1.35/1.56      inference('cnf', [status(esa)], [t23_xboole_1])).
% 1.35/1.56  thf('116', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))
% 1.35/1.56           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X0))),
% 1.35/1.56      inference('sup+', [status(thm)], ['114', '115'])).
% 1.35/1.56  thf('117', plain,
% 1.35/1.56      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 1.35/1.56      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.35/1.56  thf('118', plain,
% 1.35/1.56      (![X5 : $i, X6 : $i]:
% 1.35/1.56         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.35/1.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.35/1.56  thf('119', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.35/1.56      inference('sup-', [status(thm)], ['117', '118'])).
% 1.35/1.56  thf('120', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))
% 1.35/1.56           = (X0))),
% 1.35/1.56      inference('demod', [status(thm)], ['116', '119'])).
% 1.35/1.56  thf('121', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.35/1.56      inference('sup+', [status(thm)], ['6', '7'])).
% 1.35/1.56  thf('122', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.56         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.35/1.56      inference('sup+', [status(thm)], ['120', '121'])).
% 1.35/1.56  thf('123', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.56         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.35/1.56      inference('sup+', [status(thm)], ['113', '122'])).
% 1.35/1.56  thf('124', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.56         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0))),
% 1.35/1.56      inference('sup+', [status(thm)], ['112', '123'])).
% 1.35/1.56  thf('125', plain,
% 1.35/1.56      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)),
% 1.35/1.56      inference('sup+', [status(thm)], ['111', '124'])).
% 1.35/1.56  thf('126', plain,
% 1.35/1.56      (![X5 : $i, X6 : $i]:
% 1.35/1.56         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 1.35/1.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.35/1.56  thf('127', plain,
% 1.35/1.56      (![X0 : $i]: ((k2_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B) = (sk_B))),
% 1.35/1.56      inference('sup-', [status(thm)], ['125', '126'])).
% 1.35/1.56  thf('128', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X0 @ X1) = (k2_xboole_0 @ X1 @ X0))),
% 1.35/1.56      inference('demod', [status(thm)],
% 1.35/1.56                ['58', '61', '62', '63', '64', '67', '70'])).
% 1.35/1.56  thf('129', plain,
% 1.35/1.56      (![X0 : $i]: ((k2_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)) = (sk_B))),
% 1.35/1.56      inference('demod', [status(thm)], ['127', '128'])).
% 1.35/1.56  thf('130', plain,
% 1.35/1.56      (![X0 : $i]: ((k2_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)) = (sk_B))),
% 1.35/1.56      inference('sup+', [status(thm)], ['102', '129'])).
% 1.35/1.56  thf('131', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.35/1.56      inference('demod', [status(thm)], ['42', '43', '46', '49', '50', '51'])).
% 1.35/1.56  thf('132', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X0 @ sk_A)
% 1.35/1.56           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_B))),
% 1.35/1.56      inference('sup+', [status(thm)], ['130', '131'])).
% 1.35/1.56  thf('133', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('134', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         ((k3_xboole_0 @ X0 @ sk_A)
% 1.35/1.56           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)))),
% 1.35/1.56      inference('demod', [status(thm)], ['132', '133'])).
% 1.35/1.56  thf('135', plain, (((k1_tarski @ sk_D) = (k3_xboole_0 @ sk_C @ sk_A))),
% 1.35/1.56      inference('demod', [status(thm)], ['101', '134'])).
% 1.35/1.56  thf('136', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('137', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.35/1.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.35/1.56  thf('138', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D))),
% 1.35/1.56      inference('demod', [status(thm)], ['136', '137'])).
% 1.35/1.56  thf('139', plain, ($false),
% 1.35/1.56      inference('simplify_reflect-', [status(thm)], ['135', '138'])).
% 1.35/1.56  
% 1.35/1.56  % SZS output end Refutation
% 1.35/1.56  
% 1.35/1.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
