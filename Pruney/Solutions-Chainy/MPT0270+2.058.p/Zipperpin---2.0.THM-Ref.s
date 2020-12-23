%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pqu6lKnFmL

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:19 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 116 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  737 (1079 expanded)
%              Number of equality atoms :   57 (  84 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X5 ) )
      | ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ( r2_hidden @ ( sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,
    ( ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ( r2_hidden @ ( sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ ( k5_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','23'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('25',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('33',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('35',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X44 @ X45 )
      | ( ( k4_xboole_0 @ X45 @ ( k1_tarski @ X44 ) )
       != X45 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('36',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ~ ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','37'])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('40',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X42 ) @ X43 )
      | ( r2_hidden @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('41',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('46',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('59',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','38','39','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pqu6lKnFmL
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:37:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.66/1.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.66/1.86  % Solved by: fo/fo7.sh
% 1.66/1.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.66/1.86  % done 1698 iterations in 1.385s
% 1.66/1.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.66/1.86  % SZS output start Refutation
% 1.66/1.86  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.66/1.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.66/1.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.66/1.86  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.66/1.86  thf(sk_B_type, type, sk_B: $i > $i).
% 1.66/1.86  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.66/1.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.66/1.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.66/1.86  thf(sk_A_type, type, sk_A: $i).
% 1.66/1.86  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.66/1.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.66/1.86  thf(t67_zfmisc_1, conjecture,
% 1.66/1.86    (![A:$i,B:$i]:
% 1.66/1.86     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 1.66/1.86       ( ~( r2_hidden @ A @ B ) ) ))).
% 1.66/1.86  thf(zf_stmt_0, negated_conjecture,
% 1.66/1.86    (~( ![A:$i,B:$i]:
% 1.66/1.86        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 1.66/1.86          ( ~( r2_hidden @ A @ B ) ) ) )),
% 1.66/1.86    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 1.66/1.86  thf('0', plain,
% 1.66/1.86      (((r2_hidden @ sk_A @ sk_B_1)
% 1.66/1.86        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('1', plain,
% 1.66/1.86      (((r2_hidden @ sk_A @ sk_B_1)) | 
% 1.66/1.86       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 1.66/1.86      inference('split', [status(esa)], ['0'])).
% 1.66/1.86  thf('2', plain,
% 1.66/1.86      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 1.66/1.86      inference('split', [status(esa)], ['0'])).
% 1.66/1.86  thf('3', plain,
% 1.66/1.86      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 1.66/1.86        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 1.66/1.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.86  thf('4', plain,
% 1.66/1.86      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 1.66/1.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('split', [status(esa)], ['3'])).
% 1.66/1.86  thf(t100_xboole_1, axiom,
% 1.66/1.86    (![A:$i,B:$i]:
% 1.66/1.86     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.66/1.86  thf('5', plain,
% 1.66/1.86      (![X11 : $i, X12 : $i]:
% 1.66/1.86         ((k4_xboole_0 @ X11 @ X12)
% 1.66/1.86           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.66/1.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.66/1.86  thf(t4_xboole_0, axiom,
% 1.66/1.86    (![A:$i,B:$i]:
% 1.66/1.86     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.66/1.86            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.66/1.86       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.66/1.86            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.66/1.86  thf('6', plain,
% 1.66/1.86      (![X6 : $i, X7 : $i]:
% 1.66/1.86         ((r1_xboole_0 @ X6 @ X7)
% 1.66/1.86          | (r2_hidden @ (sk_C @ X7 @ X6) @ (k3_xboole_0 @ X6 @ X7)))),
% 1.66/1.86      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.66/1.86  thf(t1_xboole_0, axiom,
% 1.66/1.86    (![A:$i,B:$i,C:$i]:
% 1.66/1.86     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 1.66/1.86       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 1.66/1.86  thf('7', plain,
% 1.66/1.86      (![X2 : $i, X3 : $i, X5 : $i]:
% 1.66/1.86         ((r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X5))
% 1.66/1.86          | (r2_hidden @ X2 @ X3)
% 1.66/1.86          | ~ (r2_hidden @ X2 @ X5))),
% 1.66/1.86      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.66/1.86  thf('8', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         ((r1_xboole_0 @ X1 @ X0)
% 1.66/1.86          | (r2_hidden @ (sk_C @ X0 @ X1) @ X2)
% 1.66/1.86          | (r2_hidden @ (sk_C @ X0 @ X1) @ 
% 1.66/1.86             (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['6', '7'])).
% 1.66/1.86  thf('9', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         ((r2_hidden @ (sk_C @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0))
% 1.66/1.86          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 1.66/1.86          | (r1_xboole_0 @ X1 @ X0))),
% 1.66/1.86      inference('sup+', [status(thm)], ['5', '8'])).
% 1.66/1.86  thf('10', plain,
% 1.66/1.86      ((((r2_hidden @ (sk_C @ sk_B_1 @ (k1_tarski @ sk_A)) @ (k1_tarski @ sk_A))
% 1.66/1.86         | (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 1.66/1.86         | (r2_hidden @ (sk_C @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 1.66/1.86            (k1_tarski @ sk_A))))
% 1.66/1.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('sup+', [status(thm)], ['4', '9'])).
% 1.66/1.86  thf('11', plain,
% 1.66/1.86      ((((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 1.66/1.86         | (r2_hidden @ (sk_C @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 1.66/1.86            (k1_tarski @ sk_A))))
% 1.66/1.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('simplify', [status(thm)], ['10'])).
% 1.66/1.86  thf(commutativity_k3_xboole_0, axiom,
% 1.66/1.86    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.66/1.86  thf('12', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.66/1.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.66/1.86  thf('13', plain,
% 1.66/1.86      (![X6 : $i, X7 : $i]:
% 1.66/1.86         ((r1_xboole_0 @ X6 @ X7)
% 1.66/1.86          | (r2_hidden @ (sk_C @ X7 @ X6) @ (k3_xboole_0 @ X6 @ X7)))),
% 1.66/1.86      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.66/1.86  thf('14', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.66/1.86          | (r1_xboole_0 @ X0 @ X1))),
% 1.66/1.86      inference('sup+', [status(thm)], ['12', '13'])).
% 1.66/1.86  thf('15', plain,
% 1.66/1.86      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 1.66/1.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('split', [status(esa)], ['3'])).
% 1.66/1.86  thf('16', plain,
% 1.66/1.86      (![X11 : $i, X12 : $i]:
% 1.66/1.86         ((k4_xboole_0 @ X11 @ X12)
% 1.66/1.86           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.66/1.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.66/1.86  thf('17', plain,
% 1.66/1.86      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.66/1.86         (~ (r2_hidden @ X2 @ X3)
% 1.66/1.86          | ~ (r2_hidden @ X2 @ X4)
% 1.66/1.86          | ~ (r2_hidden @ X2 @ (k5_xboole_0 @ X3 @ X4)))),
% 1.66/1.86      inference('cnf', [status(esa)], [t1_xboole_0])).
% 1.66/1.86  thf('18', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 1.66/1.86          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.66/1.86          | ~ (r2_hidden @ X2 @ X1))),
% 1.66/1.86      inference('sup-', [status(thm)], ['16', '17'])).
% 1.66/1.86  thf('19', plain,
% 1.66/1.86      ((![X0 : $i]:
% 1.66/1.86          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.66/1.86           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.66/1.86           | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))))
% 1.66/1.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['15', '18'])).
% 1.66/1.86  thf('20', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.66/1.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.66/1.86  thf('21', plain,
% 1.66/1.86      ((![X0 : $i]:
% 1.66/1.86          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.66/1.86           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.66/1.86           | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))
% 1.66/1.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('demod', [status(thm)], ['19', '20'])).
% 1.66/1.86  thf('22', plain,
% 1.66/1.86      ((![X0 : $i]:
% 1.66/1.86          (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))
% 1.66/1.86           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))))
% 1.66/1.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('simplify', [status(thm)], ['21'])).
% 1.66/1.86  thf('23', plain,
% 1.66/1.86      ((((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 1.66/1.86         | ~ (r2_hidden @ (sk_C @ sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 1.66/1.86              (k1_tarski @ sk_A))))
% 1.66/1.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['14', '22'])).
% 1.66/1.86  thf('24', plain,
% 1.66/1.86      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))
% 1.66/1.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('clc', [status(thm)], ['11', '23'])).
% 1.66/1.86  thf(t7_xboole_0, axiom,
% 1.66/1.86    (![A:$i]:
% 1.66/1.86     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.66/1.86          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.66/1.86  thf('25', plain,
% 1.66/1.86      (![X10 : $i]:
% 1.66/1.86         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 1.66/1.86      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.66/1.86  thf('26', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.66/1.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.66/1.86  thf('27', plain,
% 1.66/1.86      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.66/1.86         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 1.66/1.86          | ~ (r1_xboole_0 @ X6 @ X9))),
% 1.66/1.86      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.66/1.86  thf('28', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.66/1.86          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.66/1.86      inference('sup-', [status(thm)], ['26', '27'])).
% 1.66/1.86  thf('29', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.66/1.86      inference('sup-', [status(thm)], ['25', '28'])).
% 1.66/1.86  thf('30', plain,
% 1.66/1.86      ((((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 1.66/1.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['24', '29'])).
% 1.66/1.86  thf('31', plain,
% 1.66/1.86      (![X11 : $i, X12 : $i]:
% 1.66/1.86         ((k4_xboole_0 @ X11 @ X12)
% 1.66/1.86           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.66/1.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.66/1.86  thf('32', plain,
% 1.66/1.86      ((((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))
% 1.66/1.86          = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0)))
% 1.66/1.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('sup+', [status(thm)], ['30', '31'])).
% 1.66/1.86  thf(t5_boole, axiom,
% 1.66/1.86    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.66/1.86  thf('33', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.66/1.86      inference('cnf', [status(esa)], [t5_boole])).
% 1.66/1.86  thf('34', plain,
% 1.66/1.86      ((((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1)))
% 1.66/1.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('demod', [status(thm)], ['32', '33'])).
% 1.66/1.86  thf(t65_zfmisc_1, axiom,
% 1.66/1.86    (![A:$i,B:$i]:
% 1.66/1.86     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.66/1.86       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.66/1.86  thf('35', plain,
% 1.66/1.86      (![X44 : $i, X45 : $i]:
% 1.66/1.86         (~ (r2_hidden @ X44 @ X45)
% 1.66/1.86          | ((k4_xboole_0 @ X45 @ (k1_tarski @ X44)) != (X45)))),
% 1.66/1.86      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.66/1.86  thf('36', plain,
% 1.66/1.86      (((((sk_B_1) != (sk_B_1)) | ~ (r2_hidden @ sk_A @ sk_B_1)))
% 1.66/1.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['34', '35'])).
% 1.66/1.86  thf('37', plain,
% 1.66/1.86      ((~ (r2_hidden @ sk_A @ sk_B_1))
% 1.66/1.86         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('simplify', [status(thm)], ['36'])).
% 1.66/1.86  thf('38', plain,
% 1.66/1.86      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 1.66/1.86       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['2', '37'])).
% 1.66/1.86  thf('39', plain,
% 1.66/1.86      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 1.66/1.86       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 1.66/1.86      inference('split', [status(esa)], ['3'])).
% 1.66/1.86  thf(l27_zfmisc_1, axiom,
% 1.66/1.86    (![A:$i,B:$i]:
% 1.66/1.86     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.66/1.86  thf('40', plain,
% 1.66/1.86      (![X42 : $i, X43 : $i]:
% 1.66/1.86         ((r1_xboole_0 @ (k1_tarski @ X42) @ X43) | (r2_hidden @ X42 @ X43))),
% 1.66/1.86      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.66/1.86  thf('41', plain,
% 1.66/1.86      (![X6 : $i, X7 : $i]:
% 1.66/1.86         ((r1_xboole_0 @ X6 @ X7)
% 1.66/1.86          | (r2_hidden @ (sk_C @ X7 @ X6) @ (k3_xboole_0 @ X6 @ X7)))),
% 1.66/1.86      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.66/1.86  thf('42', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.86         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.66/1.86          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.66/1.86      inference('sup-', [status(thm)], ['26', '27'])).
% 1.66/1.86  thf('43', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.66/1.86      inference('sup-', [status(thm)], ['41', '42'])).
% 1.66/1.86  thf('44', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['40', '43'])).
% 1.66/1.86  thf('45', plain,
% 1.66/1.86      (![X10 : $i]:
% 1.66/1.86         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 1.66/1.86      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.66/1.86  thf('46', plain,
% 1.66/1.86      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.66/1.86         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 1.66/1.86          | ~ (r1_xboole_0 @ X6 @ X9))),
% 1.66/1.86      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.66/1.86  thf('47', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.66/1.86      inference('sup-', [status(thm)], ['45', '46'])).
% 1.66/1.86  thf('48', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         ((r2_hidden @ X0 @ X1)
% 1.66/1.86          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['44', '47'])).
% 1.66/1.86  thf('49', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.66/1.86      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.66/1.86  thf('50', plain,
% 1.66/1.86      (![X11 : $i, X12 : $i]:
% 1.66/1.86         ((k4_xboole_0 @ X11 @ X12)
% 1.66/1.86           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.66/1.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.66/1.86  thf('51', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         ((k4_xboole_0 @ X0 @ X1)
% 1.66/1.86           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.66/1.86      inference('sup+', [status(thm)], ['49', '50'])).
% 1.66/1.86  thf('52', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.66/1.86            = (k5_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))
% 1.66/1.86          | (r2_hidden @ X0 @ X1))),
% 1.66/1.86      inference('sup+', [status(thm)], ['48', '51'])).
% 1.66/1.86  thf('53', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.66/1.86      inference('cnf', [status(esa)], [t5_boole])).
% 1.66/1.86  thf('54', plain,
% 1.66/1.86      (![X0 : $i, X1 : $i]:
% 1.66/1.86         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 1.66/1.86          | (r2_hidden @ X0 @ X1))),
% 1.66/1.86      inference('demod', [status(thm)], ['52', '53'])).
% 1.66/1.86  thf('55', plain,
% 1.66/1.86      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('split', [status(esa)], ['0'])).
% 1.66/1.86  thf('56', plain,
% 1.66/1.86      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 1.66/1.86         | (r2_hidden @ sk_A @ sk_B_1)))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('sup-', [status(thm)], ['54', '55'])).
% 1.66/1.86  thf('57', plain,
% 1.66/1.86      (((r2_hidden @ sk_A @ sk_B_1))
% 1.66/1.86         <= (~
% 1.66/1.86             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 1.66/1.86      inference('simplify', [status(thm)], ['56'])).
% 1.66/1.86  thf('58', plain,
% 1.66/1.86      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 1.66/1.86      inference('split', [status(esa)], ['3'])).
% 1.66/1.86  thf('59', plain,
% 1.66/1.86      (((r2_hidden @ sk_A @ sk_B_1)) | 
% 1.66/1.86       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 1.66/1.86      inference('sup-', [status(thm)], ['57', '58'])).
% 1.66/1.86  thf('60', plain, ($false),
% 1.66/1.86      inference('sat_resolution*', [status(thm)], ['1', '38', '39', '59'])).
% 1.66/1.86  
% 1.66/1.86  % SZS output end Refutation
% 1.66/1.86  
% 1.66/1.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
