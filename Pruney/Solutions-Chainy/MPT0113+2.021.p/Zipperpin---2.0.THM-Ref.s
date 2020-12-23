%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jVLkQiTI8t

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:31 EST 2020

% Result     : Theorem 4.29s
% Output     : Refutation 4.29s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 210 expanded)
%              Number of leaves         :   26 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          :  782 (1521 expanded)
%              Number of equality atoms :   67 ( 131 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t106_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( ( r1_tarski @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t106_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_1 )
   <= ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('13',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ sk_A @ X0 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) @ sk_A )
      | ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','36','37'])).

thf('39',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['4','38'])).

thf('40',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,(
    r1_xboole_0 @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B_1 )
    | ~ ( r1_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','43'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('45',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('52',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ X0 ) )
      = ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ X0 ) )
      = ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['50','57'])).

thf('59',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['49','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('61',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('63',plain,
    ( ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_C_1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('65',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
    = ( k3_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('69',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('71',plain,(
    ! [X25: $i] :
      ( ( k5_xboole_0 @ X25 @ X25 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('72',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ X24 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','75'])).

thf('77',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('81',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['70','75'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('84',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference('sup+',[status(thm)],['81','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['44','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jVLkQiTI8t
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.29/4.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.29/4.47  % Solved by: fo/fo7.sh
% 4.29/4.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.29/4.47  % done 3230 iterations in 4.020s
% 4.29/4.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.29/4.47  % SZS output start Refutation
% 4.29/4.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.29/4.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.29/4.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.29/4.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.29/4.47  thf(sk_B_type, type, sk_B: $i > $i).
% 4.29/4.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.29/4.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.29/4.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.29/4.47  thf(sk_A_type, type, sk_A: $i).
% 4.29/4.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.29/4.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.29/4.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.29/4.47  thf(t106_xboole_1, conjecture,
% 4.29/4.47    (![A:$i,B:$i,C:$i]:
% 4.29/4.47     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 4.29/4.47       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 4.29/4.47  thf(zf_stmt_0, negated_conjecture,
% 4.29/4.47    (~( ![A:$i,B:$i,C:$i]:
% 4.29/4.47        ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 4.29/4.47          ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) )),
% 4.29/4.47    inference('cnf.neg', [status(esa)], [t106_xboole_1])).
% 4.29/4.47  thf('0', plain,
% 4.29/4.47      ((~ (r1_tarski @ sk_A @ sk_B_1) | ~ (r1_xboole_0 @ sk_A @ sk_C_1))),
% 4.29/4.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.29/4.47  thf('1', plain,
% 4.29/4.47      ((~ (r1_tarski @ sk_A @ sk_B_1)) <= (~ ((r1_tarski @ sk_A @ sk_B_1)))),
% 4.29/4.47      inference('split', [status(esa)], ['0'])).
% 4.29/4.47  thf(commutativity_k3_xboole_0, axiom,
% 4.29/4.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.29/4.47  thf('2', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.29/4.47  thf(t4_xboole_0, axiom,
% 4.29/4.47    (![A:$i,B:$i]:
% 4.29/4.47     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 4.29/4.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 4.29/4.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 4.29/4.47            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 4.29/4.47  thf('3', plain,
% 4.29/4.47      (![X4 : $i, X5 : $i]:
% 4.29/4.47         ((r1_xboole_0 @ X4 @ X5)
% 4.29/4.47          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 4.29/4.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.29/4.47  thf('4', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]:
% 4.29/4.47         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 4.29/4.47          | (r1_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('sup+', [status(thm)], ['2', '3'])).
% 4.29/4.47  thf(t79_xboole_1, axiom,
% 4.29/4.47    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 4.29/4.47  thf('5', plain,
% 4.29/4.47      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 4.29/4.47      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.29/4.47  thf('6', plain,
% 4.29/4.47      (![X4 : $i, X5 : $i]:
% 4.29/4.47         ((r1_xboole_0 @ X4 @ X5)
% 4.29/4.47          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 4.29/4.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.29/4.47  thf('7', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.29/4.47  thf('8', plain,
% 4.29/4.47      (![X4 : $i, X6 : $i, X7 : $i]:
% 4.29/4.47         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 4.29/4.47          | ~ (r1_xboole_0 @ X4 @ X7))),
% 4.29/4.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.29/4.47  thf('9', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.29/4.47         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 4.29/4.47          | ~ (r1_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('sup-', [status(thm)], ['7', '8'])).
% 4.29/4.47  thf('10', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]:
% 4.29/4.47         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('sup-', [status(thm)], ['6', '9'])).
% 4.29/4.47  thf('11', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.29/4.47      inference('sup-', [status(thm)], ['5', '10'])).
% 4.29/4.47  thf(t7_xboole_0, axiom,
% 4.29/4.47    (![A:$i]:
% 4.29/4.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 4.29/4.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 4.29/4.47  thf('12', plain,
% 4.29/4.47      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 4.29/4.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 4.29/4.47  thf('13', plain,
% 4.29/4.47      (![X4 : $i, X6 : $i, X7 : $i]:
% 4.29/4.47         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 4.29/4.47          | ~ (r1_xboole_0 @ X4 @ X7))),
% 4.29/4.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 4.29/4.47  thf('14', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]:
% 4.29/4.47         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 4.29/4.47      inference('sup-', [status(thm)], ['12', '13'])).
% 4.29/4.47  thf('15', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]:
% 4.29/4.47         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 4.29/4.47      inference('sup-', [status(thm)], ['11', '14'])).
% 4.29/4.47  thf('16', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.29/4.47  thf('17', plain, ((r1_tarski @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 4.29/4.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.29/4.47  thf(t28_xboole_1, axiom,
% 4.29/4.47    (![A:$i,B:$i]:
% 4.29/4.47     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.29/4.47  thf('18', plain,
% 4.29/4.47      (![X14 : $i, X15 : $i]:
% 4.29/4.47         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 4.29/4.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.29/4.47  thf('19', plain,
% 4.29/4.47      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (sk_A))),
% 4.29/4.47      inference('sup-', [status(thm)], ['17', '18'])).
% 4.29/4.47  thf(t16_xboole_1, axiom,
% 4.29/4.47    (![A:$i,B:$i,C:$i]:
% 4.29/4.47     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 4.29/4.47       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 4.29/4.47  thf('20', plain,
% 4.29/4.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.29/4.47         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 4.29/4.47           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 4.29/4.47      inference('cnf', [status(esa)], [t16_xboole_1])).
% 4.29/4.47  thf('21', plain,
% 4.29/4.47      (![X0 : $i]:
% 4.29/4.47         ((k3_xboole_0 @ sk_A @ X0)
% 4.29/4.47           = (k3_xboole_0 @ sk_A @ 
% 4.29/4.47              (k3_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ X0)))),
% 4.29/4.47      inference('sup+', [status(thm)], ['19', '20'])).
% 4.29/4.47  thf('22', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.29/4.47         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 4.29/4.47          | ~ (r1_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('sup-', [status(thm)], ['7', '8'])).
% 4.29/4.47  thf('23', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]:
% 4.29/4.47         (~ (r2_hidden @ X1 @ (k3_xboole_0 @ sk_A @ X0))
% 4.29/4.47          | ~ (r1_xboole_0 @ 
% 4.29/4.47               (k3_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ X0) @ sk_A))),
% 4.29/4.47      inference('sup-', [status(thm)], ['21', '22'])).
% 4.29/4.47  thf('24', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]:
% 4.29/4.47         (~ (r1_xboole_0 @ 
% 4.29/4.47             (k3_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)) @ sk_A)
% 4.29/4.47          | ~ (r2_hidden @ X1 @ (k3_xboole_0 @ sk_A @ X0)))),
% 4.29/4.47      inference('sup-', [status(thm)], ['16', '23'])).
% 4.29/4.47  thf('25', plain,
% 4.29/4.47      (![X0 : $i]:
% 4.29/4.47         (~ (r1_xboole_0 @ k1_xboole_0 @ sk_A)
% 4.29/4.47          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_A @ sk_C_1)))),
% 4.29/4.47      inference('sup-', [status(thm)], ['15', '24'])).
% 4.29/4.47  thf('26', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.29/4.47  thf(t2_boole, axiom,
% 4.29/4.47    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 4.29/4.47  thf('27', plain,
% 4.29/4.47      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 4.29/4.47      inference('cnf', [status(esa)], [t2_boole])).
% 4.29/4.47  thf('28', plain,
% 4.29/4.47      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.29/4.47      inference('sup+', [status(thm)], ['26', '27'])).
% 4.29/4.47  thf(t100_xboole_1, axiom,
% 4.29/4.47    (![A:$i,B:$i]:
% 4.29/4.47     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.29/4.47  thf('29', plain,
% 4.29/4.47      (![X9 : $i, X10 : $i]:
% 4.29/4.47         ((k4_xboole_0 @ X9 @ X10)
% 4.29/4.47           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 4.29/4.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.29/4.47  thf('30', plain,
% 4.29/4.47      (![X0 : $i]:
% 4.29/4.47         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 4.29/4.47           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 4.29/4.47      inference('sup+', [status(thm)], ['28', '29'])).
% 4.29/4.47  thf(commutativity_k5_xboole_0, axiom,
% 4.29/4.47    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 4.29/4.47  thf('31', plain,
% 4.29/4.47      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 4.29/4.47      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 4.29/4.47  thf(t5_boole, axiom,
% 4.29/4.47    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.29/4.47  thf('32', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 4.29/4.47      inference('cnf', [status(esa)], [t5_boole])).
% 4.29/4.47  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.29/4.47      inference('sup+', [status(thm)], ['31', '32'])).
% 4.29/4.47  thf('34', plain,
% 4.29/4.47      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.29/4.47      inference('demod', [status(thm)], ['30', '33'])).
% 4.29/4.47  thf('35', plain,
% 4.29/4.47      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 4.29/4.47      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.29/4.47  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 4.29/4.47      inference('sup+', [status(thm)], ['34', '35'])).
% 4.29/4.47  thf('37', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.29/4.47  thf('38', plain,
% 4.29/4.47      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 4.29/4.47      inference('demod', [status(thm)], ['25', '36', '37'])).
% 4.29/4.47  thf('39', plain, ((r1_xboole_0 @ sk_A @ sk_C_1)),
% 4.29/4.47      inference('sup-', [status(thm)], ['4', '38'])).
% 4.29/4.47  thf('40', plain,
% 4.29/4.47      ((~ (r1_xboole_0 @ sk_A @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_A @ sk_C_1)))),
% 4.29/4.47      inference('split', [status(esa)], ['0'])).
% 4.29/4.47  thf('41', plain, (((r1_xboole_0 @ sk_A @ sk_C_1))),
% 4.29/4.47      inference('sup-', [status(thm)], ['39', '40'])).
% 4.29/4.47  thf('42', plain,
% 4.29/4.47      (~ ((r1_tarski @ sk_A @ sk_B_1)) | ~ ((r1_xboole_0 @ sk_A @ sk_C_1))),
% 4.29/4.47      inference('split', [status(esa)], ['0'])).
% 4.29/4.47  thf('43', plain, (~ ((r1_tarski @ sk_A @ sk_B_1))),
% 4.29/4.47      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 4.29/4.47  thf('44', plain, (~ (r1_tarski @ sk_A @ sk_B_1)),
% 4.29/4.47      inference('simpl_trail', [status(thm)], ['1', '43'])).
% 4.29/4.47  thf(t36_xboole_1, axiom,
% 4.29/4.47    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 4.29/4.47  thf('45', plain,
% 4.29/4.47      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 4.29/4.47      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.29/4.47  thf('46', plain,
% 4.29/4.47      (![X14 : $i, X15 : $i]:
% 4.29/4.47         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 4.29/4.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.29/4.47  thf('47', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]:
% 4.29/4.47         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 4.29/4.47           = (k4_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('sup-', [status(thm)], ['45', '46'])).
% 4.29/4.47  thf('48', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.29/4.47  thf('49', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]:
% 4.29/4.47         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.29/4.47           = (k4_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('demod', [status(thm)], ['47', '48'])).
% 4.29/4.47  thf('50', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.29/4.47  thf('51', plain,
% 4.29/4.47      (![X0 : $i]:
% 4.29/4.47         ((k3_xboole_0 @ sk_A @ X0)
% 4.29/4.47           = (k3_xboole_0 @ sk_A @ 
% 4.29/4.47              (k3_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ X0)))),
% 4.29/4.47      inference('sup+', [status(thm)], ['19', '20'])).
% 4.29/4.47  thf('52', plain,
% 4.29/4.47      (![X9 : $i, X10 : $i]:
% 4.29/4.47         ((k4_xboole_0 @ X9 @ X10)
% 4.29/4.47           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 4.29/4.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.29/4.47  thf('53', plain,
% 4.29/4.47      (![X0 : $i]:
% 4.29/4.47         ((k4_xboole_0 @ sk_A @ 
% 4.29/4.47           (k3_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ X0))
% 4.29/4.47           = (k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ X0)))),
% 4.29/4.47      inference('sup+', [status(thm)], ['51', '52'])).
% 4.29/4.47  thf('54', plain,
% 4.29/4.47      (![X9 : $i, X10 : $i]:
% 4.29/4.47         ((k4_xboole_0 @ X9 @ X10)
% 4.29/4.47           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 4.29/4.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.29/4.47  thf('55', plain,
% 4.29/4.47      (![X0 : $i]:
% 4.29/4.47         ((k4_xboole_0 @ sk_A @ 
% 4.29/4.47           (k3_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ X0))
% 4.29/4.47           = (k4_xboole_0 @ sk_A @ X0))),
% 4.29/4.47      inference('demod', [status(thm)], ['53', '54'])).
% 4.29/4.47  thf('56', plain,
% 4.29/4.47      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 4.29/4.47      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.29/4.47  thf('57', plain,
% 4.29/4.47      (![X0 : $i]:
% 4.29/4.47         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 4.29/4.47          (k3_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ X0))),
% 4.29/4.47      inference('sup+', [status(thm)], ['55', '56'])).
% 4.29/4.47  thf('58', plain,
% 4.29/4.47      (![X0 : $i]:
% 4.29/4.47         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 4.29/4.47          (k3_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 4.29/4.47      inference('sup+', [status(thm)], ['50', '57'])).
% 4.29/4.47  thf('59', plain,
% 4.29/4.47      ((r1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ 
% 4.29/4.47        (k4_xboole_0 @ sk_B_1 @ sk_C_1))),
% 4.29/4.47      inference('sup+', [status(thm)], ['49', '58'])).
% 4.29/4.47  thf('60', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]:
% 4.29/4.47         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 4.29/4.47      inference('sup-', [status(thm)], ['12', '13'])).
% 4.29/4.47  thf('61', plain,
% 4.29/4.47      (((k3_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_1) @ 
% 4.29/4.47         (k4_xboole_0 @ sk_B_1 @ sk_C_1)) = (k1_xboole_0))),
% 4.29/4.47      inference('sup-', [status(thm)], ['59', '60'])).
% 4.29/4.47  thf('62', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.29/4.47  thf('63', plain,
% 4.29/4.47      (((k3_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ 
% 4.29/4.47         (k4_xboole_0 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 4.29/4.47      inference('demod', [status(thm)], ['61', '62'])).
% 4.29/4.47  thf('64', plain,
% 4.29/4.47      (![X0 : $i]:
% 4.29/4.47         ((k3_xboole_0 @ sk_A @ X0)
% 4.29/4.47           = (k3_xboole_0 @ sk_A @ 
% 4.29/4.47              (k3_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_C_1) @ X0)))),
% 4.29/4.47      inference('sup+', [status(thm)], ['19', '20'])).
% 4.29/4.47  thf('65', plain,
% 4.29/4.47      (((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ sk_B_1))
% 4.29/4.47         = (k3_xboole_0 @ sk_A @ k1_xboole_0))),
% 4.29/4.47      inference('sup+', [status(thm)], ['63', '64'])).
% 4.29/4.47  thf('66', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]:
% 4.29/4.47         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.29/4.47           = (k4_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('demod', [status(thm)], ['47', '48'])).
% 4.29/4.47  thf('67', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.29/4.47  thf('68', plain,
% 4.29/4.47      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.29/4.47      inference('sup+', [status(thm)], ['26', '27'])).
% 4.29/4.47  thf('69', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 4.29/4.47      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 4.29/4.47  thf('70', plain,
% 4.29/4.47      (![X9 : $i, X10 : $i]:
% 4.29/4.47         ((k4_xboole_0 @ X9 @ X10)
% 4.29/4.47           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 4.29/4.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.29/4.47  thf(t92_xboole_1, axiom,
% 4.29/4.47    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 4.29/4.47  thf('71', plain, (![X25 : $i]: ((k5_xboole_0 @ X25 @ X25) = (k1_xboole_0))),
% 4.29/4.47      inference('cnf', [status(esa)], [t92_xboole_1])).
% 4.29/4.47  thf(t91_xboole_1, axiom,
% 4.29/4.47    (![A:$i,B:$i,C:$i]:
% 4.29/4.47     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 4.29/4.47       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 4.29/4.47  thf('72', plain,
% 4.29/4.47      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.29/4.47         ((k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ X24)
% 4.29/4.47           = (k5_xboole_0 @ X22 @ (k5_xboole_0 @ X23 @ X24)))),
% 4.29/4.47      inference('cnf', [status(esa)], [t91_xboole_1])).
% 4.29/4.47  thf('73', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]:
% 4.29/4.47         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 4.29/4.47           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.29/4.47      inference('sup+', [status(thm)], ['71', '72'])).
% 4.29/4.47  thf('74', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.29/4.47      inference('sup+', [status(thm)], ['31', '32'])).
% 4.29/4.47  thf('75', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]:
% 4.29/4.47         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 4.29/4.47      inference('demod', [status(thm)], ['73', '74'])).
% 4.29/4.47  thf('76', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]:
% 4.29/4.47         ((k3_xboole_0 @ X1 @ X0)
% 4.29/4.47           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.29/4.47      inference('sup+', [status(thm)], ['70', '75'])).
% 4.29/4.47  thf('77', plain,
% 4.29/4.47      (((k3_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 4.29/4.47      inference('sup+', [status(thm)], ['69', '76'])).
% 4.29/4.47  thf('78', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.29/4.47  thf('79', plain,
% 4.29/4.47      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 4.29/4.47      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 4.29/4.47  thf('80', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 4.29/4.47      inference('sup+', [status(thm)], ['31', '32'])).
% 4.29/4.47  thf('81', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_A))),
% 4.29/4.47      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 4.29/4.47  thf('82', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]:
% 4.29/4.47         ((k3_xboole_0 @ X1 @ X0)
% 4.29/4.47           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.29/4.47      inference('sup+', [status(thm)], ['70', '75'])).
% 4.29/4.47  thf('83', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]:
% 4.29/4.47         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 4.29/4.47           = (k4_xboole_0 @ X0 @ X1))),
% 4.29/4.47      inference('demod', [status(thm)], ['47', '48'])).
% 4.29/4.47  thf('84', plain,
% 4.29/4.47      (![X9 : $i, X10 : $i]:
% 4.29/4.47         ((k4_xboole_0 @ X9 @ X10)
% 4.29/4.47           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 4.29/4.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.29/4.47  thf('85', plain,
% 4.29/4.47      (![X0 : $i, X1 : $i]:
% 4.29/4.47         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 4.29/4.47           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.29/4.48      inference('sup+', [status(thm)], ['83', '84'])).
% 4.29/4.48  thf('86', plain,
% 4.29/4.48      (![X0 : $i, X1 : $i]:
% 4.29/4.48         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 4.29/4.48           = (k3_xboole_0 @ X1 @ X0))),
% 4.29/4.48      inference('sup+', [status(thm)], ['82', '85'])).
% 4.29/4.48  thf('87', plain,
% 4.29/4.48      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 4.29/4.48      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.29/4.48  thf('88', plain,
% 4.29/4.48      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 4.29/4.48      inference('sup+', [status(thm)], ['86', '87'])).
% 4.29/4.48  thf('89', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 4.29/4.48      inference('sup+', [status(thm)], ['81', '88'])).
% 4.29/4.48  thf('90', plain, ($false), inference('demod', [status(thm)], ['44', '89'])).
% 4.29/4.48  
% 4.29/4.48  % SZS output end Refutation
% 4.29/4.48  
% 4.29/4.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
