%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RLdO2uUxaS

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:25 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 505 expanded)
%              Number of leaves         :   23 ( 167 expanded)
%              Depth                    :   25
%              Number of atoms          :  644 (3673 expanded)
%              Number of equality atoms :   44 ( 335 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ X21 )
      | ( ( k4_xboole_0 @ X19 @ X21 )
       != X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ X13 @ X14 )
      | ( r1_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ X21 )
      | ( ( k4_xboole_0 @ X19 @ X21 )
       != X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_xboole_0 @ X17 @ ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('21',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(t53_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = ( k2_tarski @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ C @ B ) )
       => ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = ( k2_tarski @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_zfmisc_1])).

thf('26',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('28',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X26 @ X28 ) @ X29 )
      | ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r2_hidden @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['26','29'])).

thf(t20_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ! [D: $i] :
            ( ( ( r1_tarski @ D @ B )
              & ( r1_tarski @ D @ C ) )
           => ( r1_tarski @ D @ A ) ) )
     => ( A
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ sk_A @ sk_C )
        = ( k3_xboole_0 @ sk_B @ X0 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) @ X0 )
      | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( sk_D @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) @ ( k2_tarski @ sk_A @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('35',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ ( k2_tarski @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('37',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['26','29'])).

thf('38',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( k2_tarski @ sk_A @ sk_C )
    = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_xboole_0 @ X17 @ ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('50',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_xboole_0 @ X17 @ ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ X13 @ X14 )
      | ( r1_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ ( k2_tarski @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['39','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_xboole_0 @ X17 @ ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['0','63'])).

thf('65',plain,(
    ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != ( k2_tarski @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RLdO2uUxaS
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:57 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 404 iterations in 0.207s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.65  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(t48_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.46/0.65           = (k3_xboole_0 @ X11 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.65  thf(t2_boole, axiom,
% 0.46/0.65    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.65  thf(t46_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X9 : $i, X10 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.46/0.65  thf(t83_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (![X19 : $i, X21 : $i]:
% 0.46/0.65         ((r1_xboole_0 @ X19 @ X21) | ((k4_xboole_0 @ X19 @ X21) != (X19)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((k1_xboole_0) != (X0))
% 0.46/0.65          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X1 : $i]:
% 0.46/0.65         (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))),
% 0.46/0.65      inference('simplify', [status(thm)], ['4'])).
% 0.46/0.65  thf(t74_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.46/0.65          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.65         (~ (r1_xboole_0 @ X13 @ X14)
% 0.46/0.65          | (r1_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t74_xboole_1])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (r1_xboole_0 @ k1_xboole_0 @ 
% 0.46/0.65          (k3_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.65  thf('8', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.46/0.65      inference('sup+', [status(thm)], ['1', '7'])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i]:
% 0.46/0.65         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.46/0.65      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.65  thf(t41_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.65       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X8)
% 0.46/0.65           = (k4_xboole_0 @ X6 @ (k2_xboole_0 @ X7 @ X8)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.46/0.65           = (k4_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      (![X9 : $i, X10 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X9 @ (k2_xboole_0 @ X9 @ X10)) = (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X19 : $i, X21 : $i]:
% 0.46/0.65         ((r1_xboole_0 @ X19 @ X21) | ((k4_xboole_0 @ X19 @ X21) != (X19)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.65  thf('17', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.46/0.65      inference('simplify', [status(thm)], ['16'])).
% 0.46/0.65  thf(t81_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.46/0.65       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         ((r1_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.46/0.65          | ~ (r1_xboole_0 @ X17 @ (k4_xboole_0 @ X16 @ X18)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (r1_xboole_0 @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf('21', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i]:
% 0.46/0.65         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.46/0.65      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.46/0.65  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.65  thf(t36_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.46/0.65      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.46/0.65  thf('25', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.65      inference('sup+', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf(t53_zfmisc_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.46/0.65       ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.65        ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 0.46/0.65          ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k2_tarski @ A @ C ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t53_zfmisc_1])).
% 0.46/0.65  thf('26', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('27', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t38_zfmisc_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.46/0.65       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.46/0.65         ((r1_tarski @ (k2_tarski @ X26 @ X28) @ X29)
% 0.46/0.65          | ~ (r2_hidden @ X28 @ X29)
% 0.46/0.65          | ~ (r2_hidden @ X26 @ X29))),
% 0.46/0.65      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X0 @ sk_B)
% 0.46/0.65          | (r1_tarski @ (k2_tarski @ X0 @ sk_C) @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.65  thf('30', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '29'])).
% 0.46/0.65  thf(t20_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.46/0.65         ( ![D:$i]:
% 0.46/0.65           ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 0.46/0.65             ( r1_tarski @ D @ A ) ) ) ) =>
% 0.46/0.65       ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.65          | ~ (r1_tarski @ X0 @ X2)
% 0.46/0.65          | (r1_tarski @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.46/0.65          | ((X0) = (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k2_tarski @ sk_A @ sk_C) = (k3_xboole_0 @ sk_B @ X0))
% 0.46/0.65          | (r1_tarski @ (sk_D @ X0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)) @ X0)
% 0.46/0.65          | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (((r1_tarski @ 
% 0.46/0.65         (sk_D @ (k2_tarski @ sk_A @ sk_C) @ sk_B @ (k2_tarski @ sk_A @ sk_C)) @ 
% 0.46/0.65         (k2_tarski @ sk_A @ sk_C))
% 0.46/0.65        | ((k2_tarski @ sk_A @ sk_C)
% 0.46/0.65            = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['25', '32'])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.65          | ~ (r1_tarski @ X0 @ X2)
% 0.46/0.65          | ~ (r1_tarski @ (sk_D @ X2 @ X1 @ X0) @ X0)
% 0.46/0.65          | ((X0) = (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      ((((k2_tarski @ sk_A @ sk_C)
% 0.46/0.65          = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))
% 0.46/0.65        | ((k2_tarski @ sk_A @ sk_C)
% 0.46/0.65            = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))
% 0.46/0.65        | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ (k2_tarski @ sk_A @ sk_C))
% 0.46/0.65        | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.65  thf('36', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.46/0.65      inference('sup+', [status(thm)], ['23', '24'])).
% 0.46/0.65  thf('37', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ sk_B)),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '29'])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      ((((k2_tarski @ sk_A @ sk_C)
% 0.46/0.65          = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))
% 0.46/0.65        | ((k2_tarski @ sk_A @ sk_C)
% 0.46/0.65            = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C))))),
% 0.46/0.65      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (((k2_tarski @ sk_A @ sk_C)
% 0.46/0.65         = (k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.65  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.46/0.65           = (k3_xboole_0 @ X11 @ X12))),
% 0.46/0.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['40', '41'])).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t2_boole])).
% 0.46/0.65  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['42', '43'])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         ((r1_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.46/0.65          | ~ (r1_xboole_0 @ X17 @ (k4_xboole_0 @ X16 @ X18)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r1_xboole_0 @ X1 @ k1_xboole_0)
% 0.46/0.65          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.65  thf('47', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.65  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         ((r1_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.46/0.65          | ~ (r1_xboole_0 @ X17 @ (k4_xboole_0 @ X16 @ X18)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r1_xboole_0 @ X1 @ X0)
% 0.46/0.65          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.65  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('demod', [status(thm)], ['51', '52'])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.46/0.65      inference('sup-', [status(thm)], ['48', '53'])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.65         (~ (r1_xboole_0 @ X13 @ X14)
% 0.46/0.65          | (r1_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t74_xboole_1])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2))),
% 0.46/0.65      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ (k2_tarski @ sk_A @ sk_C))),
% 0.46/0.65      inference('sup+', [status(thm)], ['39', '56'])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.65      inference('demod', [status(thm)], ['51', '52'])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (r1_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['57', '58'])).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.65         ((r1_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 0.46/0.65          | ~ (r1_xboole_0 @ X17 @ (k4_xboole_0 @ X16 @ X18)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (r1_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.65  thf('62', plain,
% 0.46/0.65      (![X19 : $i, X20 : $i]:
% 0.46/0.65         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.46/0.65      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B))
% 0.46/0.65           = (X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.65  thf('64', plain,
% 0.46/0.65      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)
% 0.46/0.65         = (k2_tarski @ sk_A @ sk_C))),
% 0.46/0.65      inference('sup+', [status(thm)], ['0', '63'])).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B)
% 0.46/0.65         != (k2_tarski @ sk_A @ sk_C))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('66', plain, ($false),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
