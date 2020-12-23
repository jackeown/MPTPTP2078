%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XwWKqORcKe

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:54 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 191 expanded)
%              Number of leaves         :   16 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :  669 (1710 expanded)
%              Number of equality atoms :   70 ( 180 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t117_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ C @ B )
     => ( ( k4_xboole_0 @ A @ C )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ C @ B )
       => ( ( k4_xboole_0 @ A @ C )
          = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t117_xboole_1])).

thf('0',plain,(
    ( k4_xboole_0 @ sk_A @ sk_C )
 != ( k2_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('4',plain,(
    ( k4_xboole_0 @ sk_A @ sk_C )
 != ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','1','2','3'])).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('19',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ sk_B ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) @ ( k4_xboole_0 @ sk_C @ sk_B ) )
    = ( k4_xboole_0 @ sk_C @ sk_C ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X1 ) @ ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ ( k3_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('42',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('45',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k4_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32','47','48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('53',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_C @ sk_B )
    = ( k4_xboole_0 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['26','56'])).

thf('58',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ sk_C @ sk_C ) )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('61',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ( k4_xboole_0 @ sk_A @ sk_C )
 != ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['4','61'])).

thf('63',plain,(
    $false ),
    inference(simplify,[status(thm)],['62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XwWKqORcKe
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:28:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.38/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.61  % Solved by: fo/fo7.sh
% 0.38/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.61  % done 230 iterations in 0.174s
% 0.38/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.61  % SZS output start Refutation
% 0.38/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.61  thf(t117_xboole_1, conjecture,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( r1_tarski @ C @ B ) =>
% 0.38/0.61       ( ( k4_xboole_0 @ A @ C ) =
% 0.38/0.61         ( k2_xboole_0 @
% 0.38/0.61           ( k4_xboole_0 @ A @ B ) @ 
% 0.38/0.61           ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ))).
% 0.38/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.61        ( ( r1_tarski @ C @ B ) =>
% 0.38/0.61          ( ( k4_xboole_0 @ A @ C ) =
% 0.38/0.61            ( k2_xboole_0 @
% 0.38/0.61              ( k4_xboole_0 @ A @ B ) @ 
% 0.38/0.61              ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t117_xboole_1])).
% 0.38/0.61  thf('0', plain,
% 0.38/0.61      (((k4_xboole_0 @ sk_A @ sk_C)
% 0.38/0.61         != (k2_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.38/0.61             (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C))))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t52_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.38/0.61       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.38/0.61  thf('1', plain,
% 0.38/0.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 0.38/0.61           = (k2_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ 
% 0.38/0.61              (k3_xboole_0 @ X23 @ X25)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.38/0.61  thf(t48_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.38/0.61  thf('2', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.38/0.61           = (k3_xboole_0 @ X16 @ X17))),
% 0.38/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.61  thf('3', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.61  thf('4', plain,
% 0.38/0.61      (((k4_xboole_0 @ sk_A @ sk_C)
% 0.38/0.61         != (k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.38/0.61      inference('demod', [status(thm)], ['0', '1', '2', '3'])).
% 0.38/0.61  thf('5', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.38/0.61           = (k3_xboole_0 @ X16 @ X17))),
% 0.38/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.61  thf('6', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.38/0.61           = (k3_xboole_0 @ X16 @ X17))),
% 0.38/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.61  thf('7', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.61           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['5', '6'])).
% 0.38/0.61  thf(t47_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.38/0.61  thf('8', plain,
% 0.38/0.61      (![X14 : $i, X15 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.38/0.61           = (k4_xboole_0 @ X14 @ X15))),
% 0.38/0.61      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.38/0.61  thf('9', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.38/0.61           = (k4_xboole_0 @ X1 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.61  thf(t51_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.38/0.61       ( A ) ))).
% 0.38/0.61  thf('10', plain,
% 0.38/0.61      (![X21 : $i, X22 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.38/0.61           = (X21))),
% 0.38/0.61      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.38/0.61  thf('11', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.38/0.61           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))) = (X1))),
% 0.38/0.61      inference('sup+', [status(thm)], ['9', '10'])).
% 0.38/0.61  thf('12', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.38/0.61           = (k3_xboole_0 @ X16 @ X17))),
% 0.38/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.61  thf('13', plain,
% 0.38/0.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 0.38/0.61           = (k2_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ 
% 0.38/0.61              (k3_xboole_0 @ X23 @ X25)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.38/0.61  thf('14', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.38/0.61      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.38/0.61  thf('15', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.38/0.61           = (k3_xboole_0 @ X16 @ X17))),
% 0.38/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.61  thf('16', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X0 @ X0)
% 0.38/0.61           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.38/0.61  thf('17', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf(t12_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.61  thf('18', plain,
% 0.38/0.61      (![X5 : $i, X6 : $i]:
% 0.38/0.61         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.38/0.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.61  thf('19', plain, (((k2_xboole_0 @ sk_C @ sk_B) = (sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.61  thf(t41_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.38/0.61       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.38/0.61  thf('20', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.38/0.61           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.38/0.61  thf('21', plain,
% 0.38/0.61      (![X21 : $i, X22 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.38/0.61           = (X21))),
% 0.38/0.61      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.38/0.61  thf('22', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 0.38/0.61           (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.38/0.61           = (k4_xboole_0 @ X2 @ X1))),
% 0.38/0.61      inference('sup+', [status(thm)], ['20', '21'])).
% 0.38/0.61  thf('23', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ sk_B) @ 
% 0.38/0.61           (k4_xboole_0 @ X0 @ sk_B)) = (k4_xboole_0 @ X0 @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['19', '22'])).
% 0.38/0.61  thf('24', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.61  thf('25', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C)) @ 
% 0.38/0.61           (k4_xboole_0 @ X0 @ sk_B)) = (k4_xboole_0 @ X0 @ sk_C))),
% 0.38/0.61      inference('demod', [status(thm)], ['23', '24'])).
% 0.38/0.61  thf('26', plain,
% 0.38/0.61      (((k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B) @ 
% 0.38/0.61         (k4_xboole_0 @ sk_C @ sk_B)) = (k4_xboole_0 @ sk_C @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['16', '25'])).
% 0.38/0.61  thf('27', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X0 @ X0)
% 0.38/0.61           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.38/0.61  thf('28', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X0 @ X0)
% 0.38/0.61           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X1)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.38/0.61  thf('29', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.61  thf('30', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 0.38/0.61           = (k4_xboole_0 @ X0 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['28', '29'])).
% 0.38/0.61  thf('31', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ (k4_xboole_0 @ X0 @ X0))
% 0.38/0.61           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X1) @ (k4_xboole_0 @ X1 @ X1)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['27', '30'])).
% 0.38/0.61  thf('32', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.38/0.61           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.38/0.61  thf('33', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.61           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['5', '6'])).
% 0.38/0.61  thf('34', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.61  thf('35', plain,
% 0.38/0.61      (![X14 : $i, X15 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15))
% 0.38/0.61           = (k4_xboole_0 @ X14 @ X15))),
% 0.38/0.61      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.38/0.61  thf('36', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.38/0.61           = (k4_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('sup+', [status(thm)], ['34', '35'])).
% 0.38/0.61  thf('37', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))
% 0.38/0.61           = (k4_xboole_0 @ X0 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['33', '36'])).
% 0.38/0.61  thf('38', plain,
% 0.38/0.61      (![X21 : $i, X22 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.38/0.61           = (X21))),
% 0.38/0.61      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.38/0.61  thf('39', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ 
% 0.38/0.61           (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0))) = (X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['37', '38'])).
% 0.38/0.61  thf('40', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.38/0.61           = (k3_xboole_0 @ X16 @ X17))),
% 0.38/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.61  thf('41', plain,
% 0.38/0.61      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X25))
% 0.38/0.61           = (k2_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ 
% 0.38/0.61              (k3_xboole_0 @ X23 @ X25)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t52_xboole_1])).
% 0.38/0.61  thf('42', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.38/0.61           = (k3_xboole_0 @ X16 @ X17))),
% 0.38/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.61  thf('43', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.38/0.61      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.38/0.61  thf('44', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.61  thf('45', plain,
% 0.38/0.61      (![X21 : $i, X22 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k4_xboole_0 @ X21 @ X22))
% 0.38/0.61           = (X21))),
% 0.38/0.61      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.38/0.61  thf('46', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 0.38/0.61           = (X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['44', '45'])).
% 0.38/0.61  thf('47', plain,
% 0.38/0.61      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['43', '46'])).
% 0.38/0.61  thf('48', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.38/0.61           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.38/0.61  thf('49', plain,
% 0.38/0.61      (![X0 : $i]: ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['43', '46'])).
% 0.38/0.61  thf('50', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X1 @ X1))),
% 0.38/0.61      inference('demod', [status(thm)], ['31', '32', '47', '48', '49'])).
% 0.38/0.61  thf('51', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.38/0.61           = (k4_xboole_0 @ X1 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['7', '8'])).
% 0.38/0.61  thf(t17_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.38/0.61  thf('52', plain,
% 0.38/0.61      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.38/0.61      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.38/0.61  thf('53', plain,
% 0.38/0.61      (![X5 : $i, X6 : $i]:
% 0.38/0.61         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 0.38/0.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.61  thf('54', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.61  thf('55', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 0.38/0.61      inference('sup+', [status(thm)], ['51', '54'])).
% 0.38/0.61  thf('56', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X0) @ X1) = (X1))),
% 0.38/0.61      inference('sup+', [status(thm)], ['50', '55'])).
% 0.38/0.61  thf('57', plain,
% 0.38/0.61      (((k4_xboole_0 @ sk_C @ sk_B) = (k4_xboole_0 @ sk_C @ sk_C))),
% 0.38/0.61      inference('demod', [status(thm)], ['26', '56'])).
% 0.38/0.61  thf('58', plain,
% 0.38/0.61      (![X16 : $i, X17 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 0.38/0.61           = (k3_xboole_0 @ X16 @ X17))),
% 0.38/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.38/0.61  thf('59', plain,
% 0.38/0.61      (((k4_xboole_0 @ sk_C @ (k4_xboole_0 @ sk_C @ sk_C))
% 0.38/0.61         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.38/0.61      inference('sup+', [status(thm)], ['57', '58'])).
% 0.38/0.61  thf('60', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 0.38/0.61      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.38/0.61  thf('61', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['59', '60'])).
% 0.38/0.61  thf('62', plain,
% 0.38/0.61      (((k4_xboole_0 @ sk_A @ sk_C) != (k4_xboole_0 @ sk_A @ sk_C))),
% 0.38/0.61      inference('demod', [status(thm)], ['4', '61'])).
% 0.38/0.61  thf('63', plain, ($false), inference('simplify', [status(thm)], ['62'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
