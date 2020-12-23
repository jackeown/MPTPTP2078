%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2QIr2wkVYQ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:17 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 209 expanded)
%              Number of leaves         :   22 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  736 (1638 expanded)
%              Number of equality atoms :   88 ( 198 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X28
        = ( k1_tarski @ X27 ) )
      | ( X28 = k1_xboole_0 )
      | ~ ( r1_tarski @ X28 @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('14',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ ( k1_tarski @ X29 ) )
      | ( X28 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('25',plain,(
    ! [X29: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X29 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) @ sk_C ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    r1_tarski @ k1_xboole_0 @ sk_C ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('37',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('43',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X28
        = ( k1_tarski @ X27 ) )
      | ( X28 = k1_xboole_0 )
      | ~ ( r1_tarski @ X28 @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('46',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k3_xboole_0 @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ X1 )
        = ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('54',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('55',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('57',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','59'])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23','60'])).

thf('62',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference('sup+',[status(thm)],['61','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('74',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('78',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['71','79'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('81',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( ( k4_xboole_0 @ X31 @ ( k1_tarski @ X30 ) )
       != X31 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('82',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    $false ),
    inference(simplify,[status(thm)],['84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2QIr2wkVYQ
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:44:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.75/0.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.97  % Solved by: fo/fo7.sh
% 0.75/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.97  % done 1129 iterations in 0.519s
% 0.75/0.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.97  % SZS output start Refutation
% 0.75/0.97  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.97  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.97  thf(sk_D_type, type, sk_D: $i).
% 0.75/0.97  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.75/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.97  thf(t148_zfmisc_1, conjecture,
% 0.75/0.97    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.97     ( ( ( r1_tarski @ A @ B ) & 
% 0.75/0.97         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.75/0.97         ( r2_hidden @ D @ A ) ) =>
% 0.75/0.97       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.75/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.97    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.97        ( ( ( r1_tarski @ A @ B ) & 
% 0.75/0.97            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.75/0.97            ( r2_hidden @ D @ A ) ) =>
% 0.75/0.97          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.75/0.97    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.75/0.97  thf('0', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(commutativity_k3_xboole_0, axiom,
% 0.75/0.97    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.75/0.97  thf('1', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.97  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf(t28_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/0.97  thf('3', plain,
% 0.75/0.97      (![X12 : $i, X13 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.75/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.97  thf('4', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.75/0.97      inference('sup-', [status(thm)], ['2', '3'])).
% 0.75/0.97  thf('5', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.97  thf('6', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.75/0.97      inference('demod', [status(thm)], ['4', '5'])).
% 0.75/0.97  thf(t16_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i,C:$i]:
% 0.75/0.97     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.75/0.97       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.75/0.97  thf('7', plain,
% 0.75/0.97      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 0.75/0.97           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.75/0.97  thf(t17_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.75/0.97  thf('8', plain,
% 0.75/0.97      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.75/0.97      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.75/0.97  thf('9', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.97         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.75/0.97          (k3_xboole_0 @ X2 @ X1))),
% 0.75/0.97      inference('sup+', [status(thm)], ['7', '8'])).
% 0.75/0.97  thf('10', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.75/0.97      inference('sup+', [status(thm)], ['6', '9'])).
% 0.75/0.97  thf('11', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))),
% 0.75/0.97      inference('sup+', [status(thm)], ['1', '10'])).
% 0.75/0.97  thf('12', plain,
% 0.75/0.97      ((r1_tarski @ (k3_xboole_0 @ sk_C @ sk_A) @ (k1_tarski @ sk_D))),
% 0.75/0.97      inference('sup+', [status(thm)], ['0', '11'])).
% 0.75/0.97  thf(l3_zfmisc_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.75/0.97       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.75/0.97  thf('13', plain,
% 0.75/0.97      (![X27 : $i, X28 : $i]:
% 0.75/0.97         (((X28) = (k1_tarski @ X27))
% 0.75/0.97          | ((X28) = (k1_xboole_0))
% 0.75/0.97          | ~ (r1_tarski @ X28 @ (k1_tarski @ X27)))),
% 0.75/0.97      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.75/0.97  thf('14', plain,
% 0.75/0.97      ((((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 0.75/0.97        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_tarski @ sk_D)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/0.97  thf('15', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('16', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.97  thf('17', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D))),
% 0.75/0.97      inference('demod', [status(thm)], ['15', '16'])).
% 0.75/0.97  thf('18', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.75/0.97      inference('simplify_reflect-', [status(thm)], ['14', '17'])).
% 0.75/0.97  thf('19', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('20', plain,
% 0.75/0.97      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 0.75/0.97           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.75/0.97  thf('21', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ (k1_tarski @ sk_D) @ X0)
% 0.75/0.97           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['19', '20'])).
% 0.75/0.97  thf('22', plain,
% 0.75/0.97      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A)
% 0.75/0.97         = (k3_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.75/0.97      inference('sup+', [status(thm)], ['18', '21'])).
% 0.75/0.97  thf('23', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.97  thf('24', plain,
% 0.75/0.97      (![X28 : $i, X29 : $i]:
% 0.75/0.97         ((r1_tarski @ X28 @ (k1_tarski @ X29)) | ((X28) != (k1_xboole_0)))),
% 0.75/0.97      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.75/0.97  thf('25', plain,
% 0.75/0.97      (![X29 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X29))),
% 0.75/0.97      inference('simplify', [status(thm)], ['24'])).
% 0.75/0.97  thf('26', plain,
% 0.75/0.97      (![X12 : $i, X13 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.75/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.97  thf('27', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['25', '26'])).
% 0.75/0.97  thf('28', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('29', plain,
% 0.75/0.97      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 0.75/0.97           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.75/0.97  thf('30', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.97  thf('31', plain,
% 0.75/0.97      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.75/0.97      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.75/0.97  thf('32', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.75/0.97      inference('sup+', [status(thm)], ['30', '31'])).
% 0.75/0.97  thf('33', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.97         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0)),
% 0.75/0.97      inference('sup+', [status(thm)], ['29', '32'])).
% 0.75/0.97  thf('34', plain,
% 0.75/0.97      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D)) @ sk_C)),
% 0.75/0.97      inference('sup+', [status(thm)], ['28', '33'])).
% 0.75/0.97  thf('35', plain, ((r1_tarski @ k1_xboole_0 @ sk_C)),
% 0.75/0.97      inference('sup+', [status(thm)], ['27', '34'])).
% 0.75/0.97  thf('36', plain,
% 0.75/0.97      (![X12 : $i, X13 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.75/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.97  thf('37', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_C) = (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['35', '36'])).
% 0.75/0.97  thf('38', plain,
% 0.75/0.97      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 0.75/0.97           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.75/0.97  thf('39', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.97  thf('40', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 0.75/0.97           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['38', '39'])).
% 0.75/0.97  thf('41', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 0.75/0.97           = (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['37', '40'])).
% 0.75/0.97  thf('42', plain,
% 0.75/0.97      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.75/0.97      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.75/0.97  thf('43', plain,
% 0.75/0.97      (![X27 : $i, X28 : $i]:
% 0.75/0.97         (((X28) = (k1_tarski @ X27))
% 0.75/0.97          | ((X28) = (k1_xboole_0))
% 0.75/0.97          | ~ (r1_tarski @ X28 @ (k1_tarski @ X27)))),
% 0.75/0.97      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.75/0.97  thf('44', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.75/0.97          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.75/0.97      inference('sup-', [status(thm)], ['42', '43'])).
% 0.75/0.97  thf('45', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['25', '26'])).
% 0.75/0.97  thf('46', plain,
% 0.75/0.97      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ (k3_xboole_0 @ X7 @ X8) @ X9)
% 0.75/0.97           = (k3_xboole_0 @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.75/0.97  thf('47', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.75/0.97           = (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['45', '46'])).
% 0.75/0.97  thf('48', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ k1_xboole_0 @ X1)
% 0.75/0.97            = (k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))
% 0.75/0.97          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['44', '47'])).
% 0.75/0.97  thf('49', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['25', '26'])).
% 0.75/0.97  thf('50', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 0.75/0.97          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.75/0.97      inference('demod', [status(thm)], ['48', '49'])).
% 0.75/0.97  thf('51', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.75/0.97           = (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['45', '46'])).
% 0.75/0.97  thf('52', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.75/0.97            = (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.75/0.97          | ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['50', '51'])).
% 0.75/0.97  thf('53', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['25', '26'])).
% 0.75/0.97  thf('54', plain,
% 0.75/0.97      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.75/0.97      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.75/0.97  thf('55', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.75/0.97      inference('sup+', [status(thm)], ['53', '54'])).
% 0.75/0.97  thf('56', plain,
% 0.75/0.97      (![X12 : $i, X13 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.75/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.97  thf('57', plain,
% 0.75/0.97      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['55', '56'])).
% 0.75/0.97  thf('58', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.75/0.97          | ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.75/0.97      inference('demod', [status(thm)], ['52', '57'])).
% 0.75/0.97  thf('59', plain,
% 0.75/0.97      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.75/0.97      inference('simplify', [status(thm)], ['58'])).
% 0.75/0.97  thf('60', plain,
% 0.75/0.97      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.97      inference('demod', [status(thm)], ['41', '59'])).
% 0.75/0.97  thf('61', plain,
% 0.75/0.97      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k1_xboole_0))),
% 0.75/0.97      inference('demod', [status(thm)], ['22', '23', '60'])).
% 0.75/0.97  thf('62', plain,
% 0.75/0.97      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.75/0.97      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.75/0.97  thf('63', plain,
% 0.75/0.97      (![X12 : $i, X13 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.75/0.97      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.75/0.97  thf('64', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.75/0.97           = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('sup-', [status(thm)], ['62', '63'])).
% 0.75/0.97  thf('65', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.97  thf('66', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.75/0.97           = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('demod', [status(thm)], ['64', '65'])).
% 0.75/0.97  thf(t100_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.75/0.97  thf('67', plain,
% 0.75/0.97      (![X5 : $i, X6 : $i]:
% 0.75/0.97         ((k4_xboole_0 @ X5 @ X6)
% 0.75/0.97           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.97  thf('68', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.75/0.97           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['66', '67'])).
% 0.75/0.97  thf('69', plain,
% 0.75/0.97      (![X5 : $i, X6 : $i]:
% 0.75/0.97         ((k4_xboole_0 @ X5 @ X6)
% 0.75/0.97           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.75/0.97  thf('70', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.75/0.97           = (k4_xboole_0 @ X1 @ X0))),
% 0.75/0.97      inference('demod', [status(thm)], ['68', '69'])).
% 0.75/0.97  thf('71', plain,
% 0.75/0.97      (((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.75/0.97         = (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))),
% 0.75/0.97      inference('sup+', [status(thm)], ['61', '70'])).
% 0.75/0.97  thf('72', plain,
% 0.75/0.97      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.75/0.97      inference('simplify', [status(thm)], ['58'])).
% 0.75/0.97  thf('73', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.75/0.97  thf(d7_xboole_0, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.75/0.97       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.75/0.97  thf('74', plain,
% 0.75/0.97      (![X2 : $i, X4 : $i]:
% 0.75/0.97         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.75/0.97      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.75/0.97  thf('75', plain,
% 0.75/0.97      (![X0 : $i, X1 : $i]:
% 0.75/0.97         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.75/0.97      inference('sup-', [status(thm)], ['73', '74'])).
% 0.75/0.97  thf('76', plain,
% 0.75/0.97      (![X0 : $i]:
% 0.75/0.97         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['72', '75'])).
% 0.75/0.97  thf('77', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.75/0.97      inference('simplify', [status(thm)], ['76'])).
% 0.75/0.97  thf(t83_xboole_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.75/0.97  thf('78', plain,
% 0.75/0.97      (![X14 : $i, X15 : $i]:
% 0.75/0.97         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.75/0.97      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.75/0.97  thf('79', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.75/0.97      inference('sup-', [status(thm)], ['77', '78'])).
% 0.75/0.97  thf('80', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ (k1_tarski @ sk_D)))),
% 0.75/0.97      inference('demod', [status(thm)], ['71', '79'])).
% 0.75/0.97  thf(t65_zfmisc_1, axiom,
% 0.75/0.97    (![A:$i,B:$i]:
% 0.75/0.97     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.75/0.97       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.75/0.97  thf('81', plain,
% 0.75/0.97      (![X30 : $i, X31 : $i]:
% 0.75/0.97         (~ (r2_hidden @ X30 @ X31)
% 0.75/0.97          | ((k4_xboole_0 @ X31 @ (k1_tarski @ X30)) != (X31)))),
% 0.75/0.97      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.75/0.97  thf('82', plain, ((((sk_A) != (sk_A)) | ~ (r2_hidden @ sk_D @ sk_A))),
% 0.75/0.97      inference('sup-', [status(thm)], ['80', '81'])).
% 0.75/0.97  thf('83', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.75/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.97  thf('84', plain, (((sk_A) != (sk_A))),
% 0.75/0.97      inference('demod', [status(thm)], ['82', '83'])).
% 0.75/0.97  thf('85', plain, ($false), inference('simplify', [status(thm)], ['84'])).
% 0.75/0.97  
% 0.75/0.97  % SZS output end Refutation
% 0.75/0.97  
% 0.75/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
