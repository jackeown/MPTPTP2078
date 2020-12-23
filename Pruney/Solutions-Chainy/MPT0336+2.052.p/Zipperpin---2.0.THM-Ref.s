%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Nx55CpLcDV

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:27 EST 2020

% Result     : Theorem 2.71s
% Output     : Refutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 287 expanded)
%              Number of leaves         :   22 (  97 expanded)
%              Depth                    :   30
%              Number of atoms          :  819 (2383 expanded)
%              Number of equality atoms :   70 ( 181 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('6',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X51 ) @ X52 )
      | ( r2_hidden @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('28',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('29',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['29'])).

thf(t76_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ X17 @ X18 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X19 @ X17 ) @ ( k3_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t76_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_B ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['26','32'])).

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

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('42',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t116_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('44',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t116_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('51',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    r1_xboole_0 @ k1_xboole_0 @ sk_B ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('54',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['25','56'])).

thf('58',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t116_xboole_1])).

thf('59',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('60',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ ( k3_xboole_0 @ X9 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k3_xboole_0 @ sk_C_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('69',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('70',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k3_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','79'])).

thf('81',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','80'])).

thf('82',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('83',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['83'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('85',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ X20 @ X21 )
      | ( ( k3_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
        = ( k3_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','88'])).

thf('90',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['0','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Nx55CpLcDV
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:37:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.71/2.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.71/2.90  % Solved by: fo/fo7.sh
% 2.71/2.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.71/2.90  % done 2286 iterations in 2.444s
% 2.71/2.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.71/2.90  % SZS output start Refutation
% 2.71/2.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.71/2.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.71/2.90  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.71/2.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.71/2.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.71/2.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.71/2.90  thf(sk_A_type, type, sk_A: $i).
% 2.71/2.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.71/2.90  thf(sk_D_type, type, sk_D: $i).
% 2.71/2.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.71/2.90  thf(sk_B_type, type, sk_B: $i).
% 2.71/2.90  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.71/2.90  thf(t149_zfmisc_1, conjecture,
% 2.71/2.90    (![A:$i,B:$i,C:$i,D:$i]:
% 2.71/2.90     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.71/2.90         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.71/2.90       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.71/2.90  thf(zf_stmt_0, negated_conjecture,
% 2.71/2.90    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.71/2.90        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.71/2.90            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.71/2.90          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 2.71/2.90    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 2.71/2.90  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.71/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.90  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.71/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.90  thf(d7_xboole_0, axiom,
% 2.71/2.90    (![A:$i,B:$i]:
% 2.71/2.90     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.71/2.90       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.71/2.90  thf('2', plain,
% 2.71/2.90      (![X2 : $i, X3 : $i]:
% 2.71/2.90         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 2.71/2.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.71/2.90  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 2.71/2.90      inference('sup-', [status(thm)], ['1', '2'])).
% 2.71/2.90  thf(commutativity_k3_xboole_0, axiom,
% 2.71/2.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.71/2.90  thf('4', plain,
% 2.71/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.71/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.71/2.90  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 2.71/2.90      inference('demod', [status(thm)], ['3', '4'])).
% 2.71/2.90  thf(l27_zfmisc_1, axiom,
% 2.71/2.90    (![A:$i,B:$i]:
% 2.71/2.90     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 2.71/2.90  thf('6', plain,
% 2.71/2.90      (![X51 : $i, X52 : $i]:
% 2.71/2.90         ((r1_xboole_0 @ (k1_tarski @ X51) @ X52) | (r2_hidden @ X51 @ X52))),
% 2.71/2.90      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 2.71/2.90  thf('7', plain,
% 2.71/2.90      (![X2 : $i, X3 : $i]:
% 2.71/2.90         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 2.71/2.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.71/2.90  thf('8', plain,
% 2.71/2.90      (![X0 : $i, X1 : $i]:
% 2.71/2.90         ((r2_hidden @ X1 @ X0)
% 2.71/2.90          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 2.71/2.90      inference('sup-', [status(thm)], ['6', '7'])).
% 2.71/2.90  thf('9', plain,
% 2.71/2.90      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 2.71/2.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.90  thf('10', plain,
% 2.71/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.71/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.71/2.90  thf('11', plain,
% 2.71/2.90      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 2.71/2.90      inference('demod', [status(thm)], ['9', '10'])).
% 2.71/2.90  thf(t28_xboole_1, axiom,
% 2.71/2.90    (![A:$i,B:$i]:
% 2.71/2.90     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.71/2.90  thf('12', plain,
% 2.71/2.90      (![X15 : $i, X16 : $i]:
% 2.71/2.90         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 2.71/2.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.71/2.90  thf('13', plain,
% 2.71/2.90      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 2.71/2.90         = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.71/2.90      inference('sup-', [status(thm)], ['11', '12'])).
% 2.71/2.90  thf('14', plain,
% 2.71/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.71/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.71/2.90  thf('15', plain,
% 2.71/2.90      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 2.71/2.90         = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.71/2.90      inference('demod', [status(thm)], ['13', '14'])).
% 2.71/2.90  thf('16', plain,
% 2.71/2.90      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))
% 2.71/2.90        | (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 2.71/2.90      inference('sup+', [status(thm)], ['8', '15'])).
% 2.71/2.90  thf('17', plain,
% 2.71/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.71/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.71/2.90  thf('18', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 2.71/2.90      inference('demod', [status(thm)], ['3', '4'])).
% 2.71/2.90  thf(t16_xboole_1, axiom,
% 2.71/2.90    (![A:$i,B:$i,C:$i]:
% 2.71/2.90     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 2.71/2.90       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.71/2.90  thf('19', plain,
% 2.71/2.90      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.71/2.90         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 2.71/2.90           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 2.71/2.90      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.71/2.90  thf('20', plain,
% 2.71/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.71/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.71/2.90  thf('21', plain,
% 2.71/2.90      (![X2 : $i, X4 : $i]:
% 2.71/2.90         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 2.71/2.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.71/2.90  thf('22', plain,
% 2.71/2.90      (![X0 : $i, X1 : $i]:
% 2.71/2.90         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 2.71/2.90      inference('sup-', [status(thm)], ['20', '21'])).
% 2.71/2.90  thf('23', plain,
% 2.71/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.71/2.90         (((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 2.71/2.90          | (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 2.71/2.90      inference('sup-', [status(thm)], ['19', '22'])).
% 2.71/2.90  thf('24', plain,
% 2.71/2.90      (![X0 : $i]:
% 2.71/2.90         (((k3_xboole_0 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 2.71/2.90          | (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 2.71/2.90      inference('sup-', [status(thm)], ['18', '23'])).
% 2.71/2.90  thf('25', plain,
% 2.71/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.71/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.71/2.90  thf('26', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 2.71/2.90      inference('demod', [status(thm)], ['3', '4'])).
% 2.71/2.90  thf('27', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 2.71/2.90      inference('demod', [status(thm)], ['3', '4'])).
% 2.71/2.90  thf('28', plain,
% 2.71/2.90      (![X2 : $i, X4 : $i]:
% 2.71/2.90         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 2.71/2.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.71/2.90  thf('29', plain,
% 2.71/2.90      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 2.71/2.90      inference('sup-', [status(thm)], ['27', '28'])).
% 2.71/2.90  thf('30', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 2.71/2.90      inference('simplify', [status(thm)], ['29'])).
% 2.71/2.90  thf(t76_xboole_1, axiom,
% 2.71/2.90    (![A:$i,B:$i,C:$i]:
% 2.71/2.90     ( ( r1_xboole_0 @ A @ B ) =>
% 2.71/2.90       ( r1_xboole_0 @ ( k3_xboole_0 @ C @ A ) @ ( k3_xboole_0 @ C @ B ) ) ))).
% 2.71/2.90  thf('31', plain,
% 2.71/2.90      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.71/2.90         (~ (r1_xboole_0 @ X17 @ X18)
% 2.71/2.90          | (r1_xboole_0 @ (k3_xboole_0 @ X19 @ X17) @ 
% 2.71/2.90             (k3_xboole_0 @ X19 @ X18)))),
% 2.71/2.90      inference('cnf', [status(esa)], [t76_xboole_1])).
% 2.71/2.90  thf('32', plain,
% 2.71/2.90      (![X0 : $i]:
% 2.71/2.90         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ (k3_xboole_0 @ X0 @ sk_C_1))),
% 2.71/2.90      inference('sup-', [status(thm)], ['30', '31'])).
% 2.71/2.90  thf('33', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_B) @ k1_xboole_0)),
% 2.71/2.90      inference('sup+', [status(thm)], ['26', '32'])).
% 2.71/2.90  thf(t3_xboole_0, axiom,
% 2.71/2.90    (![A:$i,B:$i]:
% 2.71/2.90     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.71/2.90            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.71/2.90       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.71/2.90            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.71/2.90  thf('34', plain,
% 2.71/2.90      (![X5 : $i, X6 : $i]:
% 2.71/2.90         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 2.71/2.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.71/2.90  thf('35', plain,
% 2.71/2.90      (![X5 : $i, X6 : $i]:
% 2.71/2.90         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X6))),
% 2.71/2.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.71/2.90  thf('36', plain,
% 2.71/2.90      (![X5 : $i, X7 : $i, X8 : $i]:
% 2.71/2.90         (~ (r2_hidden @ X7 @ X5)
% 2.71/2.90          | ~ (r2_hidden @ X7 @ X8)
% 2.71/2.90          | ~ (r1_xboole_0 @ X5 @ X8))),
% 2.71/2.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.71/2.90  thf('37', plain,
% 2.71/2.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.71/2.90         ((r1_xboole_0 @ X1 @ X0)
% 2.71/2.90          | ~ (r1_xboole_0 @ X0 @ X2)
% 2.71/2.90          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 2.71/2.90      inference('sup-', [status(thm)], ['35', '36'])).
% 2.71/2.90  thf('38', plain,
% 2.71/2.90      (![X0 : $i, X1 : $i]:
% 2.71/2.90         ((r1_xboole_0 @ X0 @ X1)
% 2.71/2.90          | ~ (r1_xboole_0 @ X1 @ X0)
% 2.71/2.90          | (r1_xboole_0 @ X0 @ X1))),
% 2.71/2.90      inference('sup-', [status(thm)], ['34', '37'])).
% 2.71/2.90  thf('39', plain,
% 2.71/2.90      (![X0 : $i, X1 : $i]:
% 2.71/2.90         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 2.71/2.90      inference('simplify', [status(thm)], ['38'])).
% 2.71/2.90  thf('40', plain, ((r1_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_B))),
% 2.71/2.90      inference('sup-', [status(thm)], ['33', '39'])).
% 2.71/2.90  thf('41', plain,
% 2.71/2.90      (![X2 : $i, X3 : $i]:
% 2.71/2.90         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 2.71/2.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.71/2.90  thf('42', plain,
% 2.71/2.90      (((k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_B))
% 2.71/2.90         = (k1_xboole_0))),
% 2.71/2.90      inference('sup-', [status(thm)], ['40', '41'])).
% 2.71/2.90  thf('43', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 2.71/2.90      inference('demod', [status(thm)], ['3', '4'])).
% 2.71/2.90  thf(t116_xboole_1, axiom,
% 2.71/2.90    (![A:$i,B:$i,C:$i]:
% 2.71/2.90     ( ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 2.71/2.90       ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 2.71/2.90  thf('44', plain,
% 2.71/2.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.71/2.90         ((k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11))
% 2.71/2.90           = (k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)))),
% 2.71/2.90      inference('cnf', [status(esa)], [t116_xboole_1])).
% 2.71/2.90  thf('45', plain,
% 2.71/2.90      (![X0 : $i]:
% 2.71/2.90         ((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0))
% 2.71/2.90           = (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0)))),
% 2.71/2.90      inference('sup+', [status(thm)], ['43', '44'])).
% 2.71/2.90  thf('46', plain,
% 2.71/2.90      (![X0 : $i, X1 : $i]:
% 2.71/2.90         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 2.71/2.90      inference('sup-', [status(thm)], ['20', '21'])).
% 2.71/2.90  thf('47', plain,
% 2.71/2.90      (![X0 : $i]:
% 2.71/2.90         (((k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0))
% 2.71/2.90            != (k1_xboole_0))
% 2.71/2.90          | (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B))),
% 2.71/2.90      inference('sup-', [status(thm)], ['45', '46'])).
% 2.71/2.90  thf('48', plain,
% 2.71/2.90      ((((k1_xboole_0) != (k1_xboole_0))
% 2.71/2.90        | (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_B) @ sk_B))),
% 2.71/2.90      inference('sup-', [status(thm)], ['42', '47'])).
% 2.71/2.90  thf('49', plain,
% 2.71/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.71/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.71/2.90  thf('50', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 2.71/2.90      inference('demod', [status(thm)], ['3', '4'])).
% 2.71/2.90  thf('51', plain,
% 2.71/2.90      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ sk_B))),
% 2.71/2.90      inference('demod', [status(thm)], ['48', '49', '50'])).
% 2.71/2.90  thf('52', plain, ((r1_xboole_0 @ k1_xboole_0 @ sk_B)),
% 2.71/2.90      inference('simplify', [status(thm)], ['51'])).
% 2.71/2.90  thf('53', plain,
% 2.71/2.90      (![X2 : $i, X3 : $i]:
% 2.71/2.90         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 2.71/2.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.71/2.90  thf('54', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 2.71/2.90      inference('sup-', [status(thm)], ['52', '53'])).
% 2.71/2.90  thf('55', plain,
% 2.71/2.90      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.71/2.90         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 2.71/2.90           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 2.71/2.90      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.71/2.90  thf('56', plain,
% 2.71/2.90      (![X0 : $i]:
% 2.71/2.90         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 2.71/2.90           = (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0)))),
% 2.71/2.90      inference('sup+', [status(thm)], ['54', '55'])).
% 2.71/2.90  thf('57', plain,
% 2.71/2.90      (![X0 : $i]:
% 2.71/2.90         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 2.71/2.90           = (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 2.71/2.90      inference('sup+', [status(thm)], ['25', '56'])).
% 2.71/2.90  thf('58', plain,
% 2.71/2.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.71/2.90         ((k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11))
% 2.71/2.90           = (k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ (k3_xboole_0 @ X9 @ X11)))),
% 2.71/2.90      inference('cnf', [status(esa)], [t116_xboole_1])).
% 2.71/2.90  thf('59', plain,
% 2.71/2.90      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.71/2.90         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 2.71/2.90           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 2.71/2.90      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.71/2.90  thf('60', plain,
% 2.71/2.90      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.71/2.90         ((k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11))
% 2.71/2.90           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ (k3_xboole_0 @ X9 @ X11))))),
% 2.71/2.90      inference('demod', [status(thm)], ['58', '59'])).
% 2.71/2.90  thf('61', plain,
% 2.71/2.90      (![X0 : $i]:
% 2.71/2.90         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ sk_B))
% 2.71/2.90           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 2.71/2.90      inference('sup+', [status(thm)], ['57', '60'])).
% 2.71/2.90  thf('62', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 2.71/2.90      inference('sup-', [status(thm)], ['52', '53'])).
% 2.71/2.90  thf('63', plain,
% 2.71/2.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.71/2.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.71/2.90  thf('64', plain,
% 2.71/2.90      (![X0 : $i]:
% 2.71/2.90         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ (k3_xboole_0 @ X0 @ sk_C_1))),
% 2.71/2.90      inference('sup-', [status(thm)], ['30', '31'])).
% 2.71/2.90  thf('65', plain,
% 2.71/2.90      (![X0 : $i]:
% 2.71/2.90         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ (k3_xboole_0 @ sk_C_1 @ X0))),
% 2.71/2.90      inference('sup+', [status(thm)], ['63', '64'])).
% 2.71/2.90  thf('66', plain,
% 2.71/2.90      (![X2 : $i, X3 : $i]:
% 2.71/2.90         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 2.71/2.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.71/2.90  thf('67', plain,
% 2.71/2.90      (![X0 : $i]:
% 2.71/2.90         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 2.71/2.90           (k3_xboole_0 @ sk_C_1 @ X0)) = (k1_xboole_0))),
% 2.71/2.90      inference('sup-', [status(thm)], ['65', '66'])).
% 2.71/2.91  thf('68', plain,
% 2.71/2.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.71/2.91         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 2.71/2.91           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 2.71/2.91      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.71/2.91  thf('69', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 2.71/2.91      inference('demod', [status(thm)], ['3', '4'])).
% 2.71/2.91  thf('70', plain,
% 2.71/2.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.71/2.91         ((k3_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ X14)
% 2.71/2.91           = (k3_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14)))),
% 2.71/2.91      inference('cnf', [status(esa)], [t16_xboole_1])).
% 2.71/2.91  thf('71', plain,
% 2.71/2.91      (![X0 : $i]:
% 2.71/2.91         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 2.71/2.91           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 2.71/2.91      inference('sup+', [status(thm)], ['69', '70'])).
% 2.71/2.91  thf('72', plain,
% 2.71/2.91      (![X0 : $i]:
% 2.71/2.91         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 2.71/2.91      inference('demod', [status(thm)], ['67', '68', '71'])).
% 2.71/2.91  thf('73', plain,
% 2.71/2.91      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.71/2.91      inference('demod', [status(thm)], ['61', '62', '72'])).
% 2.71/2.91  thf('74', plain,
% 2.71/2.91      (![X0 : $i]:
% 2.71/2.91         (((k1_xboole_0) != (k1_xboole_0))
% 2.71/2.91          | (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 2.71/2.91      inference('demod', [status(thm)], ['24', '73'])).
% 2.71/2.91  thf('75', plain,
% 2.71/2.91      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B))),
% 2.71/2.91      inference('simplify', [status(thm)], ['74'])).
% 2.71/2.91  thf('76', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 2.71/2.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.71/2.91  thf('77', plain,
% 2.71/2.91      (![X5 : $i, X7 : $i, X8 : $i]:
% 2.71/2.91         (~ (r2_hidden @ X7 @ X5)
% 2.71/2.91          | ~ (r2_hidden @ X7 @ X8)
% 2.71/2.91          | ~ (r1_xboole_0 @ X5 @ X8))),
% 2.71/2.91      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.71/2.91  thf('78', plain,
% 2.71/2.91      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 2.71/2.91      inference('sup-', [status(thm)], ['76', '77'])).
% 2.71/2.91  thf('79', plain,
% 2.71/2.91      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ X0 @ sk_B))),
% 2.71/2.91      inference('sup-', [status(thm)], ['75', '78'])).
% 2.71/2.91  thf('80', plain,
% 2.71/2.91      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 2.71/2.91      inference('sup-', [status(thm)], ['17', '79'])).
% 2.71/2.91  thf('81', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.71/2.91      inference('sup-', [status(thm)], ['16', '80'])).
% 2.71/2.91  thf('82', plain,
% 2.71/2.91      (![X2 : $i, X4 : $i]:
% 2.71/2.91         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 2.71/2.91      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.71/2.91  thf('83', plain,
% 2.71/2.91      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 2.71/2.91      inference('sup-', [status(thm)], ['81', '82'])).
% 2.71/2.91  thf('84', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 2.71/2.91      inference('simplify', [status(thm)], ['83'])).
% 2.71/2.91  thf(t78_xboole_1, axiom,
% 2.71/2.91    (![A:$i,B:$i,C:$i]:
% 2.71/2.91     ( ( r1_xboole_0 @ A @ B ) =>
% 2.71/2.91       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 2.71/2.91         ( k3_xboole_0 @ A @ C ) ) ))).
% 2.71/2.91  thf('85', plain,
% 2.71/2.91      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.71/2.91         (~ (r1_xboole_0 @ X20 @ X21)
% 2.71/2.91          | ((k3_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 2.71/2.91              = (k3_xboole_0 @ X20 @ X22)))),
% 2.71/2.91      inference('cnf', [status(esa)], [t78_xboole_1])).
% 2.71/2.91  thf('86', plain,
% 2.71/2.91      (![X0 : $i]:
% 2.71/2.91         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 2.71/2.91           = (k3_xboole_0 @ sk_B @ X0))),
% 2.71/2.91      inference('sup-', [status(thm)], ['84', '85'])).
% 2.71/2.91  thf('87', plain,
% 2.71/2.91      (![X0 : $i, X1 : $i]:
% 2.71/2.91         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 2.71/2.91      inference('sup-', [status(thm)], ['20', '21'])).
% 2.71/2.91  thf('88', plain,
% 2.71/2.91      (![X0 : $i]:
% 2.71/2.91         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 2.71/2.91          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 2.71/2.91      inference('sup-', [status(thm)], ['86', '87'])).
% 2.71/2.91  thf('89', plain,
% 2.71/2.91      ((((k1_xboole_0) != (k1_xboole_0))
% 2.71/2.91        | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B))),
% 2.71/2.91      inference('sup-', [status(thm)], ['5', '88'])).
% 2.71/2.91  thf('90', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.71/2.91      inference('simplify', [status(thm)], ['89'])).
% 2.71/2.91  thf('91', plain, ($false), inference('demod', [status(thm)], ['0', '90'])).
% 2.71/2.91  
% 2.71/2.91  % SZS output end Refutation
% 2.71/2.91  
% 2.71/2.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
