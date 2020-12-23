%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.02vvxABg8n

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:26 EST 2020

% Result     : Theorem 3.73s
% Output     : Refutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  181 (6521 expanded)
%              Number of leaves         :   26 (2072 expanded)
%              Depth                    :   48
%              Number of atoms          : 1236 (42899 expanded)
%              Number of equality atoms :   82 (1820 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('3',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) ) @ ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['1','23'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('34',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','28'])).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['41'])).

thf('43',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','28'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('48',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ k1_xboole_0 ) ) @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','42'])).

thf('55',plain,
    ( ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('57',plain,
    ( ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('59',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('61',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('63',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','65'])).

thf('67',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','42'])).

thf('68',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','42'])).

thf('69',plain,(
    v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','70'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('72',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('73',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('74',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X19 ) @ ( k4_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('75',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','80'])).

thf('82',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','42'])).

thf('83',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','42'])).

thf('84',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('85',plain,(
    ! [X16: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X16 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('86',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X19 ) @ ( k4_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','42'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k4_relat_1 @ k1_xboole_0 )
      = ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','90'])).

thf('92',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('93',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','42'])).

thf('94',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','94'])).

thf('96',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X19 ) @ ( k4_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('100',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','28'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['99','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','104'])).

thf('106',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('107',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','42'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ! [X16: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X16 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X16: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X16 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('114',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('115',plain,(
    ! [X16: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X16 ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('116',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X19 ) @ ( k4_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','42'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['113','125'])).

thf('127',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['112','128'])).

thf('130',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('131',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['131'])).

thf('133',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['130','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('135',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('136',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['131'])).

thf('139',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('142',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['140','141'])).

thf('143',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['134','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['131'])).

thf('147',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_A )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['133','147'])).

thf('149',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('152',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    $false ),
    inference(simplify,[status(thm)],['152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.02vvxABg8n
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.73/3.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.73/3.93  % Solved by: fo/fo7.sh
% 3.73/3.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.73/3.93  % done 3385 iterations in 3.472s
% 3.73/3.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.73/3.93  % SZS output start Refutation
% 3.73/3.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.73/3.93  thf(sk_A_type, type, sk_A: $i).
% 3.73/3.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.73/3.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.73/3.93  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.73/3.93  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 3.73/3.93  thf(sk_B_type, type, sk_B: $i > $i).
% 3.73/3.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.73/3.93  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.73/3.93  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.73/3.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.73/3.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.73/3.93  thf(l13_xboole_0, axiom,
% 3.73/3.93    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.73/3.93  thf('0', plain,
% 3.73/3.93      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 3.73/3.93      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.73/3.93  thf(cc1_relat_1, axiom,
% 3.73/3.93    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 3.73/3.93  thf('1', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 3.73/3.93      inference('cnf', [status(esa)], [cc1_relat_1])).
% 3.73/3.93  thf(dt_k5_relat_1, axiom,
% 3.73/3.93    (![A:$i,B:$i]:
% 3.73/3.93     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 3.73/3.93       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 3.73/3.93  thf('2', plain,
% 3.73/3.93      (![X13 : $i, X14 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X13)
% 3.73/3.93          | ~ (v1_relat_1 @ X14)
% 3.73/3.93          | (v1_relat_1 @ (k5_relat_1 @ X13 @ X14)))),
% 3.73/3.93      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 3.73/3.93  thf('3', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 3.73/3.93      inference('cnf', [status(esa)], [cc1_relat_1])).
% 3.73/3.93  thf(t60_relat_1, axiom,
% 3.73/3.93    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 3.73/3.93     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 3.73/3.93  thf('4', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.73/3.93      inference('cnf', [status(esa)], [t60_relat_1])).
% 3.73/3.93  thf(t45_relat_1, axiom,
% 3.73/3.93    (![A:$i]:
% 3.73/3.93     ( ( v1_relat_1 @ A ) =>
% 3.73/3.93       ( ![B:$i]:
% 3.73/3.93         ( ( v1_relat_1 @ B ) =>
% 3.73/3.93           ( r1_tarski @
% 3.73/3.93             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 3.73/3.93  thf('5', plain,
% 3.73/3.93      (![X17 : $i, X18 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X17)
% 3.73/3.93          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X18 @ X17)) @ 
% 3.73/3.93             (k2_relat_1 @ X17))
% 3.73/3.93          | ~ (v1_relat_1 @ X18))),
% 3.73/3.93      inference('cnf', [status(esa)], [t45_relat_1])).
% 3.73/3.93  thf('6', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 3.73/3.93           k1_xboole_0)
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ k1_xboole_0))),
% 3.73/3.93      inference('sup+', [status(thm)], ['4', '5'])).
% 3.73/3.93  thf('7', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 3.73/3.93             k1_xboole_0))),
% 3.73/3.93      inference('sup-', [status(thm)], ['3', '6'])).
% 3.73/3.93  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.73/3.93  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.73/3.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.73/3.93  thf('9', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 3.73/3.93             k1_xboole_0))),
% 3.73/3.93      inference('demod', [status(thm)], ['7', '8'])).
% 3.73/3.93  thf(d3_tarski, axiom,
% 3.73/3.93    (![A:$i,B:$i]:
% 3.73/3.93     ( ( r1_tarski @ A @ B ) <=>
% 3.73/3.93       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.73/3.93  thf('10', plain,
% 3.73/3.93      (![X4 : $i, X6 : $i]:
% 3.73/3.93         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.73/3.93      inference('cnf', [status(esa)], [d3_tarski])).
% 3.73/3.93  thf(d1_xboole_0, axiom,
% 3.73/3.93    (![A:$i]:
% 3.73/3.93     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.73/3.93  thf('11', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.73/3.93      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.73/3.93  thf('12', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.73/3.93      inference('sup-', [status(thm)], ['10', '11'])).
% 3.73/3.93  thf(d10_xboole_0, axiom,
% 3.73/3.93    (![A:$i,B:$i]:
% 3.73/3.93     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.73/3.93  thf('13', plain,
% 3.73/3.93      (![X8 : $i, X10 : $i]:
% 3.73/3.93         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 3.73/3.93      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.73/3.93  thf('14', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.73/3.93      inference('sup-', [status(thm)], ['12', '13'])).
% 3.73/3.93  thf('15', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 3.73/3.93          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.73/3.93      inference('sup-', [status(thm)], ['9', '14'])).
% 3.73/3.93  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.73/3.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.73/3.93  thf('17', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 3.73/3.93      inference('demod', [status(thm)], ['15', '16'])).
% 3.73/3.93  thf(fc9_relat_1, axiom,
% 3.73/3.93    (![A:$i]:
% 3.73/3.93     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 3.73/3.93       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 3.73/3.93  thf('18', plain,
% 3.73/3.93      (![X15 : $i]:
% 3.73/3.93         (~ (v1_xboole_0 @ (k2_relat_1 @ X15))
% 3.73/3.93          | ~ (v1_relat_1 @ X15)
% 3.73/3.93          | (v1_xboole_0 @ X15))),
% 3.73/3.93      inference('cnf', [status(esa)], [fc9_relat_1])).
% 3.73/3.93  thf('19', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 3.73/3.93          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 3.73/3.93      inference('sup-', [status(thm)], ['17', '18'])).
% 3.73/3.93  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.73/3.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.73/3.93  thf('21', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 3.73/3.93          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 3.73/3.93      inference('demod', [status(thm)], ['19', '20'])).
% 3.73/3.93  thf('22', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ k1_xboole_0)
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 3.73/3.93          | ~ (v1_relat_1 @ X0))),
% 3.73/3.93      inference('sup-', [status(thm)], ['2', '21'])).
% 3.73/3.93  thf('23', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ k1_xboole_0))),
% 3.73/3.93      inference('simplify', [status(thm)], ['22'])).
% 3.73/3.93  thf('24', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 3.73/3.93      inference('sup-', [status(thm)], ['1', '23'])).
% 3.73/3.93  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.73/3.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.73/3.93  thf('26', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 3.73/3.93      inference('demod', [status(thm)], ['24', '25'])).
% 3.73/3.93  thf('27', plain,
% 3.73/3.93      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 3.73/3.93      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.73/3.93  thf('28', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 3.73/3.93      inference('sup-', [status(thm)], ['26', '27'])).
% 3.73/3.93  thf('29', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 3.73/3.93          | ~ (v1_xboole_0 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ X1))),
% 3.73/3.93      inference('sup+', [status(thm)], ['0', '28'])).
% 3.73/3.93  thf('30', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 3.73/3.93      inference('sup-', [status(thm)], ['26', '27'])).
% 3.73/3.93  thf('31', plain,
% 3.73/3.93      (![X13 : $i, X14 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X13)
% 3.73/3.93          | ~ (v1_relat_1 @ X14)
% 3.73/3.93          | (v1_relat_1 @ (k5_relat_1 @ X13 @ X14)))),
% 3.73/3.93      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 3.73/3.93  thf(t62_relat_1, conjecture,
% 3.73/3.93    (![A:$i]:
% 3.73/3.93     ( ( v1_relat_1 @ A ) =>
% 3.73/3.93       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 3.73/3.93         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 3.73/3.93  thf(zf_stmt_0, negated_conjecture,
% 3.73/3.93    (~( ![A:$i]:
% 3.73/3.93        ( ( v1_relat_1 @ A ) =>
% 3.73/3.93          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 3.73/3.93            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 3.73/3.93    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 3.73/3.93  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 3.73/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.93  thf('33', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 3.73/3.93      inference('demod', [status(thm)], ['24', '25'])).
% 3.73/3.93  thf('34', plain, (![X11 : $i]: ((v1_relat_1 @ X11) | ~ (v1_xboole_0 @ X11))),
% 3.73/3.93      inference('cnf', [status(esa)], [cc1_relat_1])).
% 3.73/3.93  thf('35', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 3.73/3.93          | ~ (v1_xboole_0 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ X1))),
% 3.73/3.93      inference('sup+', [status(thm)], ['0', '28'])).
% 3.73/3.93  thf('36', plain,
% 3.73/3.93      (![X13 : $i, X14 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X13)
% 3.73/3.93          | ~ (v1_relat_1 @ X14)
% 3.73/3.93          | (v1_relat_1 @ (k5_relat_1 @ X13 @ X14)))),
% 3.73/3.93      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 3.73/3.93  thf('37', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         ((v1_relat_1 @ k1_xboole_0)
% 3.73/3.93          | ~ (v1_relat_1 @ X1)
% 3.73/3.93          | ~ (v1_xboole_0 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ X1))),
% 3.73/3.93      inference('sup+', [status(thm)], ['35', '36'])).
% 3.73/3.93  thf('38', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_xboole_0 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ X1)
% 3.73/3.93          | (v1_relat_1 @ k1_xboole_0))),
% 3.73/3.93      inference('simplify', [status(thm)], ['37'])).
% 3.73/3.93  thf('39', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (~ (v1_xboole_0 @ X0)
% 3.73/3.93          | (v1_relat_1 @ k1_xboole_0)
% 3.73/3.93          | ~ (v1_relat_1 @ X1)
% 3.73/3.93          | ~ (v1_xboole_0 @ X0))),
% 3.73/3.93      inference('sup-', [status(thm)], ['34', '38'])).
% 3.73/3.93  thf('40', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X1)
% 3.73/3.93          | (v1_relat_1 @ k1_xboole_0)
% 3.73/3.93          | ~ (v1_xboole_0 @ X0))),
% 3.73/3.93      inference('simplify', [status(thm)], ['39'])).
% 3.73/3.93  thf('41', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | (v1_relat_1 @ k1_xboole_0)
% 3.73/3.93          | ~ (v1_relat_1 @ X1))),
% 3.73/3.93      inference('sup-', [status(thm)], ['33', '40'])).
% 3.73/3.93  thf('42', plain,
% 3.73/3.93      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 3.73/3.93      inference('condensation', [status(thm)], ['41'])).
% 3.73/3.93  thf('43', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.73/3.93      inference('sup-', [status(thm)], ['32', '42'])).
% 3.73/3.93  thf('44', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 3.73/3.93          | ~ (v1_xboole_0 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ X1))),
% 3.73/3.93      inference('sup+', [status(thm)], ['0', '28'])).
% 3.73/3.93  thf('45', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_xboole_0 @ X0)
% 3.73/3.93          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 3.73/3.93      inference('sup-', [status(thm)], ['43', '44'])).
% 3.73/3.93  thf('46', plain,
% 3.73/3.93      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.73/3.93      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.73/3.93  thf('47', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 3.73/3.93             k1_xboole_0))),
% 3.73/3.93      inference('demod', [status(thm)], ['7', '8'])).
% 3.73/3.93  thf('48', plain,
% 3.73/3.93      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.73/3.93         (~ (r2_hidden @ X3 @ X4)
% 3.73/3.93          | (r2_hidden @ X3 @ X5)
% 3.73/3.93          | ~ (r1_tarski @ X4 @ X5))),
% 3.73/3.93      inference('cnf', [status(esa)], [d3_tarski])).
% 3.73/3.93  thf('49', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | (r2_hidden @ X1 @ k1_xboole_0)
% 3.73/3.93          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 3.73/3.93      inference('sup-', [status(thm)], ['47', '48'])).
% 3.73/3.93  thf('50', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         ((v1_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 3.73/3.93          | (r2_hidden @ 
% 3.73/3.93             (sk_B @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))) @ 
% 3.73/3.93             k1_xboole_0)
% 3.73/3.93          | ~ (v1_relat_1 @ X0))),
% 3.73/3.93      inference('sup-', [status(thm)], ['46', '49'])).
% 3.73/3.93  thf('51', plain,
% 3.73/3.93      (((r2_hidden @ (sk_B @ (k2_relat_1 @ k1_xboole_0)) @ k1_xboole_0)
% 3.73/3.93        | ~ (v1_xboole_0 @ k1_xboole_0)
% 3.73/3.93        | ~ (v1_relat_1 @ k1_xboole_0)
% 3.73/3.93        | (v1_xboole_0 @ 
% 3.73/3.93           (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))))),
% 3.73/3.93      inference('sup+', [status(thm)], ['45', '50'])).
% 3.73/3.93  thf('52', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.73/3.93      inference('cnf', [status(esa)], [t60_relat_1])).
% 3.73/3.93  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.73/3.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.73/3.93  thf('54', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.73/3.93      inference('sup-', [status(thm)], ['32', '42'])).
% 3.73/3.93  thf('55', plain,
% 3.73/3.93      (((r2_hidden @ (sk_B @ k1_xboole_0) @ k1_xboole_0)
% 3.73/3.93        | (v1_xboole_0 @ 
% 3.73/3.93           (k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))))),
% 3.73/3.93      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 3.73/3.93  thf('56', plain,
% 3.73/3.93      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 3.73/3.93      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.73/3.93  thf('57', plain,
% 3.73/3.93      (((r2_hidden @ (sk_B @ k1_xboole_0) @ k1_xboole_0)
% 3.73/3.93        | ((k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 3.73/3.93            = (k1_xboole_0)))),
% 3.73/3.93      inference('sup-', [status(thm)], ['55', '56'])).
% 3.73/3.93  thf('58', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.73/3.93      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.73/3.93  thf('59', plain,
% 3.73/3.93      ((((k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 3.73/3.93          = (k1_xboole_0))
% 3.73/3.93        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.73/3.93      inference('sup-', [status(thm)], ['57', '58'])).
% 3.73/3.93  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.73/3.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.73/3.93  thf('61', plain,
% 3.73/3.93      (((k2_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)) = (k1_xboole_0))),
% 3.73/3.93      inference('demod', [status(thm)], ['59', '60'])).
% 3.73/3.93  thf('62', plain,
% 3.73/3.93      (![X15 : $i]:
% 3.73/3.93         (~ (v1_xboole_0 @ (k2_relat_1 @ X15))
% 3.73/3.93          | ~ (v1_relat_1 @ X15)
% 3.73/3.93          | (v1_xboole_0 @ X15))),
% 3.73/3.93      inference('cnf', [status(esa)], [fc9_relat_1])).
% 3.73/3.93  thf('63', plain,
% 3.73/3.93      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.73/3.93        | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 3.73/3.93        | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 3.73/3.93      inference('sup-', [status(thm)], ['61', '62'])).
% 3.73/3.93  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.73/3.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.73/3.93  thf('65', plain,
% 3.73/3.93      (((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))
% 3.73/3.93        | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 3.73/3.93      inference('demod', [status(thm)], ['63', '64'])).
% 3.73/3.93  thf('66', plain,
% 3.73/3.93      ((~ (v1_relat_1 @ k1_xboole_0)
% 3.73/3.93        | ~ (v1_relat_1 @ k1_xboole_0)
% 3.73/3.93        | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 3.73/3.93      inference('sup-', [status(thm)], ['31', '65'])).
% 3.73/3.93  thf('67', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.73/3.93      inference('sup-', [status(thm)], ['32', '42'])).
% 3.73/3.93  thf('68', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.73/3.93      inference('sup-', [status(thm)], ['32', '42'])).
% 3.73/3.93  thf('69', plain, ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 3.73/3.93      inference('demod', [status(thm)], ['66', '67', '68'])).
% 3.73/3.93  thf('70', plain,
% 3.73/3.93      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 3.73/3.93      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.73/3.93  thf('71', plain,
% 3.73/3.93      (((k5_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.73/3.93      inference('sup-', [status(thm)], ['69', '70'])).
% 3.73/3.93  thf(dt_k4_relat_1, axiom,
% 3.73/3.93    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 3.73/3.93  thf('72', plain,
% 3.73/3.93      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 3.73/3.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 3.73/3.93  thf('73', plain,
% 3.73/3.93      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 3.73/3.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 3.73/3.93  thf(t54_relat_1, axiom,
% 3.73/3.93    (![A:$i]:
% 3.73/3.93     ( ( v1_relat_1 @ A ) =>
% 3.73/3.93       ( ![B:$i]:
% 3.73/3.93         ( ( v1_relat_1 @ B ) =>
% 3.73/3.93           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 3.73/3.93             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 3.73/3.93  thf('74', plain,
% 3.73/3.93      (![X19 : $i, X20 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X19)
% 3.73/3.93          | ((k4_relat_1 @ (k5_relat_1 @ X20 @ X19))
% 3.73/3.93              = (k5_relat_1 @ (k4_relat_1 @ X19) @ (k4_relat_1 @ X20)))
% 3.73/3.93          | ~ (v1_relat_1 @ X20))),
% 3.73/3.93      inference('cnf', [status(esa)], [t54_relat_1])).
% 3.73/3.93  thf('75', plain,
% 3.73/3.93      (![X13 : $i, X14 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X13)
% 3.73/3.93          | ~ (v1_relat_1 @ X14)
% 3.73/3.93          | (v1_relat_1 @ (k5_relat_1 @ X13 @ X14)))),
% 3.73/3.93      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 3.73/3.93  thf('76', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 3.73/3.93          | ~ (v1_relat_1 @ X1)
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X1))
% 3.73/3.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 3.73/3.93      inference('sup+', [status(thm)], ['74', '75'])).
% 3.73/3.93  thf('77', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X1))
% 3.73/3.93          | ~ (v1_relat_1 @ X1)
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | (v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 3.73/3.93      inference('sup-', [status(thm)], ['73', '76'])).
% 3.73/3.93  thf('78', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 3.73/3.93          | ~ (v1_relat_1 @ X1)
% 3.73/3.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X1))
% 3.73/3.93          | ~ (v1_relat_1 @ X0))),
% 3.73/3.93      inference('simplify', [status(thm)], ['77'])).
% 3.73/3.93  thf('79', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ X1)
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | (v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 3.73/3.93      inference('sup-', [status(thm)], ['72', '78'])).
% 3.73/3.93  thf('80', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 3.73/3.93          | ~ (v1_relat_1 @ X1)
% 3.73/3.93          | ~ (v1_relat_1 @ X0))),
% 3.73/3.93      inference('simplify', [status(thm)], ['79'])).
% 3.73/3.93  thf('81', plain,
% 3.73/3.93      (((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 3.73/3.93        | ~ (v1_relat_1 @ k1_xboole_0)
% 3.73/3.93        | ~ (v1_relat_1 @ k1_xboole_0))),
% 3.73/3.93      inference('sup+', [status(thm)], ['71', '80'])).
% 3.73/3.93  thf('82', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.73/3.93      inference('sup-', [status(thm)], ['32', '42'])).
% 3.73/3.93  thf('83', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.73/3.93      inference('sup-', [status(thm)], ['32', '42'])).
% 3.73/3.93  thf('84', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 3.73/3.93      inference('demod', [status(thm)], ['81', '82', '83'])).
% 3.73/3.93  thf(involutiveness_k4_relat_1, axiom,
% 3.73/3.93    (![A:$i]:
% 3.73/3.93     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 3.73/3.93  thf('85', plain,
% 3.73/3.93      (![X16 : $i]:
% 3.73/3.93         (((k4_relat_1 @ (k4_relat_1 @ X16)) = (X16)) | ~ (v1_relat_1 @ X16))),
% 3.73/3.93      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 3.73/3.93  thf('86', plain,
% 3.73/3.93      (![X19 : $i, X20 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X19)
% 3.73/3.93          | ((k4_relat_1 @ (k5_relat_1 @ X20 @ X19))
% 3.73/3.93              = (k5_relat_1 @ (k4_relat_1 @ X19) @ (k4_relat_1 @ X20)))
% 3.73/3.93          | ~ (v1_relat_1 @ X20))),
% 3.73/3.93      inference('cnf', [status(esa)], [t54_relat_1])).
% 3.73/3.93  thf('87', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 3.73/3.93            = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 3.73/3.93          | ~ (v1_relat_1 @ X1))),
% 3.73/3.93      inference('sup+', [status(thm)], ['85', '86'])).
% 3.73/3.93  thf('88', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ k1_xboole_0)
% 3.73/3.93          | ((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ X0))
% 3.73/3.93              = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0)))),
% 3.73/3.93      inference('sup-', [status(thm)], ['84', '87'])).
% 3.73/3.93  thf('89', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.73/3.93      inference('sup-', [status(thm)], ['32', '42'])).
% 3.73/3.93  thf('90', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | ((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ X0))
% 3.73/3.93              = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0)))),
% 3.73/3.93      inference('demod', [status(thm)], ['88', '89'])).
% 3.73/3.93  thf('91', plain,
% 3.73/3.93      ((((k4_relat_1 @ k1_xboole_0)
% 3.73/3.93          = (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0))
% 3.73/3.93        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 3.73/3.93        | ~ (v1_relat_1 @ k1_xboole_0))),
% 3.73/3.93      inference('sup+', [status(thm)], ['30', '90'])).
% 3.73/3.93  thf('92', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 3.73/3.93      inference('demod', [status(thm)], ['81', '82', '83'])).
% 3.73/3.93  thf('93', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.73/3.93      inference('sup-', [status(thm)], ['32', '42'])).
% 3.73/3.93  thf('94', plain,
% 3.73/3.93      (((k4_relat_1 @ k1_xboole_0)
% 3.73/3.93         = (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0))),
% 3.73/3.93      inference('demod', [status(thm)], ['91', '92', '93'])).
% 3.73/3.93  thf('95', plain,
% 3.73/3.93      ((((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 3.73/3.93        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 3.73/3.93        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.73/3.93      inference('sup+', [status(thm)], ['29', '94'])).
% 3.73/3.93  thf('96', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 3.73/3.93      inference('demod', [status(thm)], ['81', '82', '83'])).
% 3.73/3.93  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.73/3.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.73/3.93  thf('98', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.73/3.93      inference('demod', [status(thm)], ['95', '96', '97'])).
% 3.73/3.93  thf('99', plain,
% 3.73/3.93      (![X19 : $i, X20 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X19)
% 3.73/3.93          | ((k4_relat_1 @ (k5_relat_1 @ X20 @ X19))
% 3.73/3.93              = (k5_relat_1 @ (k4_relat_1 @ X19) @ (k4_relat_1 @ X20)))
% 3.73/3.93          | ~ (v1_relat_1 @ X20))),
% 3.73/3.93      inference('cnf', [status(esa)], [t54_relat_1])).
% 3.73/3.93  thf('100', plain,
% 3.73/3.93      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 3.73/3.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 3.73/3.93  thf('101', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 3.73/3.93          | ~ (v1_xboole_0 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ X1))),
% 3.73/3.93      inference('sup+', [status(thm)], ['0', '28'])).
% 3.73/3.93  thf('102', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_xboole_0 @ X1)
% 3.73/3.93          | ((k5_relat_1 @ (k4_relat_1 @ X0) @ X1) = (k1_xboole_0)))),
% 3.73/3.93      inference('sup-', [status(thm)], ['100', '101'])).
% 3.73/3.93  thf('103', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (((k4_relat_1 @ (k5_relat_1 @ X1 @ X0)) = (k1_xboole_0))
% 3.73/3.93          | ~ (v1_relat_1 @ X1)
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_xboole_0 @ (k4_relat_1 @ X1))
% 3.73/3.93          | ~ (v1_relat_1 @ X0))),
% 3.73/3.93      inference('sup+', [status(thm)], ['99', '102'])).
% 3.73/3.93  thf('104', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (~ (v1_xboole_0 @ (k4_relat_1 @ X1))
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ X1)
% 3.73/3.93          | ((k4_relat_1 @ (k5_relat_1 @ X1 @ X0)) = (k1_xboole_0)))),
% 3.73/3.93      inference('simplify', [status(thm)], ['103'])).
% 3.73/3.93  thf('105', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.73/3.93          | ((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 3.73/3.93          | ~ (v1_relat_1 @ k1_xboole_0)
% 3.73/3.93          | ~ (v1_relat_1 @ X0))),
% 3.73/3.93      inference('sup-', [status(thm)], ['98', '104'])).
% 3.73/3.93  thf('106', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.73/3.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.73/3.93  thf('107', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.73/3.93      inference('sup-', [status(thm)], ['32', '42'])).
% 3.73/3.93  thf('108', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 3.73/3.93          | ~ (v1_relat_1 @ X0))),
% 3.73/3.93      inference('demod', [status(thm)], ['105', '106', '107'])).
% 3.73/3.93  thf('109', plain,
% 3.73/3.93      (![X16 : $i]:
% 3.73/3.93         (((k4_relat_1 @ (k4_relat_1 @ X16)) = (X16)) | ~ (v1_relat_1 @ X16))),
% 3.73/3.93      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 3.73/3.93  thf('110', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 3.73/3.93      inference('sup+', [status(thm)], ['108', '109'])).
% 3.73/3.93  thf('111', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.73/3.93      inference('demod', [status(thm)], ['95', '96', '97'])).
% 3.73/3.93  thf('112', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 3.73/3.93      inference('demod', [status(thm)], ['110', '111'])).
% 3.73/3.93  thf('113', plain,
% 3.73/3.93      (![X16 : $i]:
% 3.73/3.93         (((k4_relat_1 @ (k4_relat_1 @ X16)) = (X16)) | ~ (v1_relat_1 @ X16))),
% 3.73/3.93      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 3.73/3.93  thf('114', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 3.73/3.93      inference('demod', [status(thm)], ['81', '82', '83'])).
% 3.73/3.93  thf('115', plain,
% 3.73/3.93      (![X16 : $i]:
% 3.73/3.93         (((k4_relat_1 @ (k4_relat_1 @ X16)) = (X16)) | ~ (v1_relat_1 @ X16))),
% 3.73/3.93      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 3.73/3.93  thf('116', plain,
% 3.73/3.93      (![X19 : $i, X20 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X19)
% 3.73/3.93          | ((k4_relat_1 @ (k5_relat_1 @ X20 @ X19))
% 3.73/3.93              = (k5_relat_1 @ (k4_relat_1 @ X19) @ (k4_relat_1 @ X20)))
% 3.73/3.93          | ~ (v1_relat_1 @ X20))),
% 3.73/3.93      inference('cnf', [status(esa)], [t54_relat_1])).
% 3.73/3.93  thf('117', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 3.73/3.93            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ X1)
% 3.73/3.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 3.73/3.93      inference('sup+', [status(thm)], ['115', '116'])).
% 3.73/3.93  thf('118', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ k1_xboole_0)
% 3.73/3.93          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ k1_xboole_0)))
% 3.73/3.93              = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0))))),
% 3.73/3.93      inference('sup-', [status(thm)], ['114', '117'])).
% 3.73/3.93  thf('119', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.73/3.93      inference('sup-', [status(thm)], ['32', '42'])).
% 3.73/3.93  thf('120', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ k1_xboole_0)))
% 3.73/3.93              = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0))))),
% 3.73/3.93      inference('demod', [status(thm)], ['118', '119'])).
% 3.73/3.93  thf('121', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 3.73/3.93          | ~ (v1_relat_1 @ X1)
% 3.73/3.93          | ~ (v1_relat_1 @ X0))),
% 3.73/3.93      inference('simplify', [status(thm)], ['79'])).
% 3.73/3.93  thf('122', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         ((v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 3.73/3.93          | ~ (v1_relat_1 @ X0))),
% 3.73/3.93      inference('sup+', [status(thm)], ['120', '121'])).
% 3.73/3.93  thf('123', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 3.73/3.93      inference('demod', [status(thm)], ['81', '82', '83'])).
% 3.73/3.93  thf('124', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         ((v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ X0))),
% 3.73/3.93      inference('demod', [status(thm)], ['122', '123'])).
% 3.73/3.93  thf('125', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0))))),
% 3.73/3.93      inference('simplify', [status(thm)], ['124'])).
% 3.73/3.93  thf('126', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         ((v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 3.73/3.93          | ~ (v1_relat_1 @ X0)
% 3.73/3.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 3.73/3.93      inference('sup+', [status(thm)], ['113', '125'])).
% 3.73/3.93  thf('127', plain,
% 3.73/3.93      (![X12 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X12)) | ~ (v1_relat_1 @ X12))),
% 3.73/3.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 3.73/3.93  thf('128', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 3.73/3.93      inference('clc', [status(thm)], ['126', '127'])).
% 3.73/3.93  thf('129', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0)
% 3.73/3.93          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 3.73/3.93      inference('clc', [status(thm)], ['112', '128'])).
% 3.73/3.93  thf('130', plain,
% 3.73/3.93      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 3.73/3.93      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.73/3.93  thf('131', plain,
% 3.73/3.93      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 3.73/3.93        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 3.73/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.93  thf('132', plain,
% 3.73/3.93      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 3.73/3.93         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 3.73/3.93      inference('split', [status(esa)], ['131'])).
% 3.73/3.93  thf('133', plain,
% 3.73/3.93      ((![X0 : $i]:
% 3.73/3.93          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 3.73/3.93         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 3.73/3.93      inference('sup-', [status(thm)], ['130', '132'])).
% 3.73/3.93  thf('134', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 3.73/3.93      inference('demod', [status(thm)], ['24', '25'])).
% 3.73/3.93  thf('135', plain,
% 3.73/3.93      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 3.73/3.93      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.73/3.93  thf('136', plain,
% 3.73/3.93      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 3.73/3.93      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.73/3.93  thf('137', plain,
% 3.73/3.93      (![X0 : $i, X1 : $i]:
% 3.73/3.93         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 3.73/3.93      inference('sup+', [status(thm)], ['135', '136'])).
% 3.73/3.93  thf('138', plain,
% 3.73/3.93      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 3.73/3.93         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 3.73/3.93      inference('split', [status(esa)], ['131'])).
% 3.73/3.93  thf('139', plain,
% 3.73/3.93      ((![X0 : $i]:
% 3.73/3.93          (((X0) != (k1_xboole_0))
% 3.73/3.93           | ~ (v1_xboole_0 @ X0)
% 3.73/3.93           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 3.73/3.93         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 3.73/3.93      inference('sup-', [status(thm)], ['137', '138'])).
% 3.73/3.93  thf('140', plain,
% 3.73/3.93      (((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 3.73/3.93         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 3.73/3.93         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 3.73/3.93      inference('simplify', [status(thm)], ['139'])).
% 3.73/3.93  thf('141', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.73/3.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.73/3.93  thf('142', plain,
% 3.73/3.93      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 3.73/3.93         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 3.73/3.93      inference('simplify_reflect+', [status(thm)], ['140', '141'])).
% 3.73/3.93  thf('143', plain,
% 3.73/3.93      ((~ (v1_relat_1 @ sk_A))
% 3.73/3.93         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 3.73/3.93      inference('sup-', [status(thm)], ['134', '142'])).
% 3.73/3.93  thf('144', plain, ((v1_relat_1 @ sk_A)),
% 3.73/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.93  thf('145', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 3.73/3.93      inference('demod', [status(thm)], ['143', '144'])).
% 3.73/3.93  thf('146', plain,
% 3.73/3.93      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 3.73/3.93       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 3.73/3.93      inference('split', [status(esa)], ['131'])).
% 3.73/3.93  thf('147', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 3.73/3.93      inference('sat_resolution*', [status(thm)], ['145', '146'])).
% 3.73/3.93  thf('148', plain,
% 3.73/3.93      (![X0 : $i]:
% 3.73/3.93         (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.73/3.93      inference('simpl_trail', [status(thm)], ['133', '147'])).
% 3.73/3.93  thf('149', plain,
% 3.73/3.93      ((((k1_xboole_0) != (k1_xboole_0))
% 3.73/3.93        | ~ (v1_relat_1 @ sk_A)
% 3.73/3.93        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.73/3.93      inference('sup-', [status(thm)], ['129', '148'])).
% 3.73/3.93  thf('150', plain, ((v1_relat_1 @ sk_A)),
% 3.73/3.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.73/3.93  thf('151', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.73/3.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.73/3.93  thf('152', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 3.73/3.93      inference('demod', [status(thm)], ['149', '150', '151'])).
% 3.73/3.93  thf('153', plain, ($false), inference('simplify', [status(thm)], ['152'])).
% 3.73/3.93  
% 3.73/3.93  % SZS output end Refutation
% 3.73/3.93  
% 3.73/3.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
