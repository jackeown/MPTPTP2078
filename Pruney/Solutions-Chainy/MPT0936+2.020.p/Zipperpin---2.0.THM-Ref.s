%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5WbORuHFFz

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:25 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 147 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   19
%              Number of atoms          :  663 (1436 expanded)
%              Number of equality atoms :   85 ( 163 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X19 ) @ ( k2_tarski @ X20 @ X21 ) )
      = ( k2_tarski @ ( k4_tarski @ X19 @ X20 ) @ ( k4_tarski @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) )
        = X23 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X19 @ X20 ) @ ( k1_tarski @ X22 ) )
      = ( k2_tarski @ ( k4_tarski @ X19 @ X22 ) @ ( k4_tarski @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('6',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X2 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
        = ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_zfmisc_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('10',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_tarski @ X2 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
        = ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['8','10'])).

thf(t34_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) )
    <=> ( ( A = C )
        & ( B = D ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X18 ) ) )
      | ( X16 != X18 )
      | ( X15 != X14 ) ) ),
    inference(cnf,[status(esa)],[t34_zfmisc_1])).

thf('13',plain,(
    ! [X14: $i,X18: $i] :
      ( r2_hidden @ ( k4_tarski @ X14 @ X18 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X14 ) @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) @ ( k4_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X19 ) @ ( k2_tarski @ X20 @ X21 ) )
      = ( k2_tarski @ ( k4_tarski @ X19 @ X20 ) @ ( k4_tarski @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ ( k4_tarski @ X1 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ ( k4_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ X1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
        = ( k1_tarski @ X2 ) )
      | ( ( k1_tarski @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
        = ( k1_tarski @ X2 ) )
      | ( ( k1_tarski @ X2 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('25',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_mcart_1 @ X27 @ X28 @ X29 )
      = ( k4_tarski @ ( k4_tarski @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) )
        = X23 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) ) )
        = ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) ) )
      | ( ( k1_tarski @ ( k4_tarski @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf(t97_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
      = ( k1_tarski @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) )
        = ( k1_tarski @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t97_mcart_1])).

thf('30',plain,(
    ( k1_relat_1 @ ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ sk_A @ sk_B @ sk_C ) ) ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) )
     != ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,
    ( ( ( k1_tarski @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ ( k4_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('35',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('37',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) )
        = ( k1_tarski @ ( k4_tarski @ sk_C @ X0 ) ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ ( k4_tarski @ sk_C @ X0 ) ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ ( k4_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ sk_C @ X0 ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('49',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k1_tarski @ ( k4_tarski @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) @ ( k4_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5WbORuHFFz
% 0.15/0.34  % Computer   : n024.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:08:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.62/0.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.62/0.85  % Solved by: fo/fo7.sh
% 0.62/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.85  % done 380 iterations in 0.392s
% 0.62/0.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.62/0.85  % SZS output start Refutation
% 0.62/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.62/0.85  thf(sk_C_type, type, sk_C: $i).
% 0.62/0.85  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.62/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.85  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.62/0.85  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.62/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.62/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.85  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.62/0.85  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.62/0.85  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.62/0.85  thf(t36_zfmisc_1, axiom,
% 0.62/0.85    (![A:$i,B:$i,C:$i]:
% 0.62/0.85     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.62/0.85         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.62/0.85       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.62/0.85         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.62/0.85  thf('0', plain,
% 0.62/0.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.62/0.85         ((k2_zfmisc_1 @ (k1_tarski @ X19) @ (k2_tarski @ X20 @ X21))
% 0.62/0.85           = (k2_tarski @ (k4_tarski @ X19 @ X20) @ (k4_tarski @ X19 @ X21)))),
% 0.62/0.85      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.62/0.85  thf(t69_enumset1, axiom,
% 0.62/0.85    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.62/0.85  thf('1', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.62/0.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.62/0.85  thf('2', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]:
% 0.62/0.85         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 0.62/0.85           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.62/0.85      inference('sup+', [status(thm)], ['0', '1'])).
% 0.62/0.85  thf(t195_relat_1, axiom,
% 0.62/0.85    (![A:$i,B:$i]:
% 0.62/0.85     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.62/0.85          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.62/0.85               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.62/0.85  thf('3', plain,
% 0.62/0.85      (![X23 : $i, X24 : $i]:
% 0.62/0.85         (((X23) = (k1_xboole_0))
% 0.62/0.85          | ((k1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24)) = (X23))
% 0.62/0.85          | ((X24) = (k1_xboole_0)))),
% 0.62/0.85      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.62/0.85  thf('4', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]:
% 0.62/0.85         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.62/0.85            = (k1_tarski @ X1))
% 0.62/0.85          | ((k2_tarski @ X0 @ X0) = (k1_xboole_0))
% 0.62/0.85          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.62/0.85      inference('sup+', [status(thm)], ['2', '3'])).
% 0.62/0.85  thf('5', plain,
% 0.62/0.85      (![X19 : $i, X20 : $i, X22 : $i]:
% 0.62/0.85         ((k2_zfmisc_1 @ (k2_tarski @ X19 @ X20) @ (k1_tarski @ X22))
% 0.62/0.85           = (k2_tarski @ (k4_tarski @ X19 @ X22) @ (k4_tarski @ X20 @ X22)))),
% 0.62/0.85      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.62/0.85  thf('6', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.62/0.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.62/0.85  thf('7', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]:
% 0.62/0.85         ((k2_zfmisc_1 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0))
% 0.62/0.85           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.62/0.85      inference('sup+', [status(thm)], ['5', '6'])).
% 0.62/0.85  thf('8', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.85         (((k2_zfmisc_1 @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.62/0.85            = (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.62/0.85          | ((k1_tarski @ X2) = (k1_xboole_0))
% 0.62/0.85          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 0.62/0.85              = (k1_tarski @ X2)))),
% 0.62/0.85      inference('sup+', [status(thm)], ['4', '7'])).
% 0.62/0.85  thf(t113_zfmisc_1, axiom,
% 0.62/0.85    (![A:$i,B:$i]:
% 0.62/0.85     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.62/0.85       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.62/0.85  thf('9', plain,
% 0.62/0.85      (![X12 : $i, X13 : $i]:
% 0.62/0.85         (((k2_zfmisc_1 @ X12 @ X13) = (k1_xboole_0))
% 0.62/0.85          | ((X12) != (k1_xboole_0)))),
% 0.62/0.85      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.62/0.85  thf('10', plain,
% 0.62/0.85      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.62/0.85      inference('simplify', [status(thm)], ['9'])).
% 0.62/0.85  thf('11', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.85         (((k1_xboole_0) = (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.62/0.85          | ((k1_tarski @ X2) = (k1_xboole_0))
% 0.62/0.85          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 0.62/0.85              = (k1_tarski @ X2)))),
% 0.62/0.85      inference('demod', [status(thm)], ['8', '10'])).
% 0.62/0.85  thf(t34_zfmisc_1, axiom,
% 0.62/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.85     ( ( r2_hidden @
% 0.62/0.85         ( k4_tarski @ A @ B ) @ 
% 0.62/0.85         ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ ( k1_tarski @ D ) ) ) <=>
% 0.62/0.85       ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ))).
% 0.62/0.85  thf('12', plain,
% 0.62/0.85      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.62/0.85         ((r2_hidden @ (k4_tarski @ X15 @ X16) @ 
% 0.62/0.85           (k2_zfmisc_1 @ (k1_tarski @ X14) @ (k1_tarski @ X18)))
% 0.62/0.85          | ((X16) != (X18))
% 0.62/0.85          | ((X15) != (X14)))),
% 0.62/0.85      inference('cnf', [status(esa)], [t34_zfmisc_1])).
% 0.62/0.85  thf('13', plain,
% 0.62/0.85      (![X14 : $i, X18 : $i]:
% 0.62/0.85         (r2_hidden @ (k4_tarski @ X14 @ X18) @ 
% 0.62/0.85          (k2_zfmisc_1 @ (k1_tarski @ X14) @ (k1_tarski @ X18)))),
% 0.62/0.85      inference('simplify', [status(thm)], ['12'])).
% 0.62/0.85  thf(t7_ordinal1, axiom,
% 0.62/0.85    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.62/0.85  thf('14', plain,
% 0.62/0.85      (![X25 : $i, X26 : $i]:
% 0.62/0.85         (~ (r2_hidden @ X25 @ X26) | ~ (r1_tarski @ X26 @ X25))),
% 0.62/0.85      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.62/0.85  thf('15', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]:
% 0.62/0.85         ~ (r1_tarski @ (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0)) @ 
% 0.62/0.85            (k4_tarski @ X1 @ X0))),
% 0.62/0.85      inference('sup-', [status(thm)], ['13', '14'])).
% 0.62/0.85  thf('16', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.62/0.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.62/0.85  thf('17', plain,
% 0.62/0.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.62/0.85         ((k2_zfmisc_1 @ (k1_tarski @ X19) @ (k2_tarski @ X20 @ X21))
% 0.62/0.85           = (k2_tarski @ (k4_tarski @ X19 @ X20) @ (k4_tarski @ X19 @ X21)))),
% 0.62/0.85      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.62/0.85  thf('18', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]:
% 0.62/0.85         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.62/0.85           = (k2_tarski @ (k4_tarski @ X1 @ X0) @ (k4_tarski @ X1 @ X0)))),
% 0.62/0.85      inference('sup+', [status(thm)], ['16', '17'])).
% 0.62/0.85  thf('19', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.62/0.85      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.62/0.85  thf('20', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]:
% 0.62/0.85         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.62/0.85           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.62/0.85      inference('demod', [status(thm)], ['18', '19'])).
% 0.62/0.85  thf('21', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]:
% 0.62/0.85         ~ (r1_tarski @ (k1_tarski @ (k4_tarski @ X1 @ X0)) @ 
% 0.62/0.85            (k4_tarski @ X1 @ X0))),
% 0.62/0.85      inference('demod', [status(thm)], ['15', '20'])).
% 0.62/0.85  thf('22', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.85         (~ (r1_tarski @ k1_xboole_0 @ (k4_tarski @ X1 @ X0))
% 0.62/0.85          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 0.62/0.85              = (k1_tarski @ X2))
% 0.62/0.85          | ((k1_tarski @ X2) = (k1_xboole_0)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['11', '21'])).
% 0.62/0.85  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.62/0.85  thf('23', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.62/0.85      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.62/0.85  thf('24', plain,
% 0.62/0.85      (![X1 : $i, X2 : $i]:
% 0.62/0.85         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 0.62/0.85            = (k1_tarski @ X2))
% 0.62/0.85          | ((k1_tarski @ X2) = (k1_xboole_0)))),
% 0.62/0.85      inference('demod', [status(thm)], ['22', '23'])).
% 0.62/0.85  thf(d3_mcart_1, axiom,
% 0.62/0.85    (![A:$i,B:$i,C:$i]:
% 0.62/0.85     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.62/0.85  thf('25', plain,
% 0.62/0.85      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.62/0.85         ((k3_mcart_1 @ X27 @ X28 @ X29)
% 0.62/0.85           = (k4_tarski @ (k4_tarski @ X27 @ X28) @ X29))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.62/0.85  thf('26', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]:
% 0.62/0.85         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.62/0.85           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.62/0.85      inference('demod', [status(thm)], ['18', '19'])).
% 0.62/0.85  thf('27', plain,
% 0.62/0.85      (![X23 : $i, X24 : $i]:
% 0.62/0.85         (((X23) = (k1_xboole_0))
% 0.62/0.85          | ((k1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24)) = (X23))
% 0.62/0.85          | ((X24) = (k1_xboole_0)))),
% 0.62/0.85      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.62/0.85  thf('28', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]:
% 0.62/0.85         (((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.62/0.85            = (k1_tarski @ X1))
% 0.62/0.85          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.62/0.85          | ((k1_tarski @ X1) = (k1_xboole_0)))),
% 0.62/0.85      inference('sup+', [status(thm)], ['26', '27'])).
% 0.62/0.85  thf('29', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.85         (((k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0)))
% 0.62/0.85            = (k1_tarski @ (k4_tarski @ X2 @ X1)))
% 0.62/0.85          | ((k1_tarski @ (k4_tarski @ X2 @ X1)) = (k1_xboole_0))
% 0.62/0.85          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.62/0.85      inference('sup+', [status(thm)], ['25', '28'])).
% 0.62/0.85  thf(t97_mcart_1, conjecture,
% 0.62/0.85    (![A:$i,B:$i,C:$i]:
% 0.62/0.85     ( ( k1_relat_1 @
% 0.62/0.85         ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.62/0.85       ( k1_tarski @ A ) ))).
% 0.62/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.85    (~( ![A:$i,B:$i,C:$i]:
% 0.62/0.85        ( ( k1_relat_1 @
% 0.62/0.85            ( k1_relat_1 @ ( k1_tarski @ ( k3_mcart_1 @ A @ B @ C ) ) ) ) =
% 0.62/0.85          ( k1_tarski @ A ) ) )),
% 0.62/0.85    inference('cnf.neg', [status(esa)], [t97_mcart_1])).
% 0.62/0.85  thf('30', plain,
% 0.62/0.85      (((k1_relat_1 @ 
% 0.62/0.85         (k1_relat_1 @ (k1_tarski @ (k3_mcart_1 @ sk_A @ sk_B @ sk_C))))
% 0.62/0.85         != (k1_tarski @ sk_A))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('31', plain,
% 0.62/0.85      ((((k1_relat_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))
% 0.62/0.85          != (k1_tarski @ sk_A))
% 0.62/0.85        | ((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.62/0.85        | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B)) = (k1_xboole_0)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['29', '30'])).
% 0.62/0.85  thf('32', plain,
% 0.62/0.85      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.62/0.85        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.62/0.85        | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.62/0.85        | ((k1_tarski @ sk_C) = (k1_xboole_0)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['24', '31'])).
% 0.62/0.85  thf('33', plain,
% 0.62/0.85      ((((k1_tarski @ sk_C) = (k1_xboole_0))
% 0.62/0.85        | ((k1_tarski @ (k4_tarski @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.62/0.85        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.62/0.85      inference('simplify', [status(thm)], ['32'])).
% 0.62/0.85  thf('34', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]:
% 0.62/0.85         ~ (r1_tarski @ (k1_tarski @ (k4_tarski @ X1 @ X0)) @ 
% 0.62/0.85            (k4_tarski @ X1 @ X0))),
% 0.62/0.85      inference('demod', [status(thm)], ['15', '20'])).
% 0.62/0.85  thf('35', plain,
% 0.62/0.85      ((~ (r1_tarski @ k1_xboole_0 @ (k4_tarski @ sk_A @ sk_B))
% 0.62/0.85        | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.62/0.85        | ((k1_tarski @ sk_C) = (k1_xboole_0)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['33', '34'])).
% 0.62/0.85  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.62/0.85      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.62/0.85  thf('37', plain,
% 0.62/0.85      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.62/0.85        | ((k1_tarski @ sk_C) = (k1_xboole_0)))),
% 0.62/0.85      inference('demod', [status(thm)], ['35', '36'])).
% 0.62/0.85  thf('38', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]:
% 0.62/0.85         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 0.62/0.85           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.62/0.85      inference('sup+', [status(thm)], ['0', '1'])).
% 0.62/0.85  thf('39', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         (((k2_zfmisc_1 @ k1_xboole_0 @ (k2_tarski @ X0 @ X0))
% 0.62/0.85            = (k1_tarski @ (k4_tarski @ sk_C @ X0)))
% 0.62/0.85          | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.62/0.85      inference('sup+', [status(thm)], ['37', '38'])).
% 0.62/0.85  thf('40', plain,
% 0.62/0.85      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.62/0.85      inference('simplify', [status(thm)], ['9'])).
% 0.62/0.85  thf('41', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         (((k1_xboole_0) = (k1_tarski @ (k4_tarski @ sk_C @ X0)))
% 0.62/0.85          | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.62/0.85      inference('demod', [status(thm)], ['39', '40'])).
% 0.62/0.85  thf('42', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]:
% 0.62/0.85         ~ (r1_tarski @ (k1_tarski @ (k4_tarski @ X1 @ X0)) @ 
% 0.62/0.85            (k4_tarski @ X1 @ X0))),
% 0.62/0.85      inference('demod', [status(thm)], ['15', '20'])).
% 0.62/0.85  thf('43', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         (~ (r1_tarski @ k1_xboole_0 @ (k4_tarski @ sk_C @ X0))
% 0.62/0.85          | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['41', '42'])).
% 0.62/0.85  thf('44', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.62/0.85      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.62/0.85  thf('45', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.62/0.85      inference('demod', [status(thm)], ['43', '44'])).
% 0.62/0.85  thf('46', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]:
% 0.62/0.85         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 0.62/0.85           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.62/0.85      inference('sup+', [status(thm)], ['0', '1'])).
% 0.62/0.85  thf('47', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         ((k2_zfmisc_1 @ k1_xboole_0 @ (k2_tarski @ X0 @ X0))
% 0.62/0.85           = (k1_tarski @ (k4_tarski @ sk_A @ X0)))),
% 0.62/0.85      inference('sup+', [status(thm)], ['45', '46'])).
% 0.62/0.85  thf('48', plain,
% 0.62/0.85      (![X13 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.62/0.85      inference('simplify', [status(thm)], ['9'])).
% 0.62/0.85  thf('49', plain,
% 0.62/0.85      (![X0 : $i]: ((k1_xboole_0) = (k1_tarski @ (k4_tarski @ sk_A @ X0)))),
% 0.62/0.85      inference('demod', [status(thm)], ['47', '48'])).
% 0.62/0.85  thf('50', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]:
% 0.62/0.85         ~ (r1_tarski @ (k1_tarski @ (k4_tarski @ X1 @ X0)) @ 
% 0.62/0.85            (k4_tarski @ X1 @ X0))),
% 0.62/0.85      inference('demod', [status(thm)], ['15', '20'])).
% 0.62/0.85  thf('51', plain,
% 0.62/0.85      (![X0 : $i]: ~ (r1_tarski @ k1_xboole_0 @ (k4_tarski @ sk_A @ X0))),
% 0.62/0.85      inference('sup-', [status(thm)], ['49', '50'])).
% 0.62/0.85  thf('52', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.62/0.85      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.62/0.85  thf('53', plain, ($false), inference('demod', [status(thm)], ['51', '52'])).
% 0.62/0.85  
% 0.62/0.85  % SZS output end Refutation
% 0.62/0.85  
% 0.62/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
